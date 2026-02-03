{-# LANGUAGE DeriveGeneric #-}
{- |
   Module      : Pomc.Prob.GGraph
   Copyright   : 2023-2025 Francesco Pontiggia
   License     : MIT
   Maintainer  : Francesco Pontiggia
-}

module Pomc.Prob.GGraph ( GNode(..)
                        , qualitativeModelCheck
                        , quantitativeModelCheck
                        ) where

import Pomc.Prob.ProbUtils hiding (sIdMap, SIdGen)
import Pomc.SatUtil(SIdGen, SatState(..))
import Pomc.TimeUtils (startTimer, stopTimer)
import Pomc.LogUtils (MonadLogger, logInfoN)
import qualified Pomc.SatUtil as SU
import Pomc.State(State(..))
import Pomc.Prec (Prec(..))
import Pomc.Potl(Formula(..))
import Pomc.PropConv(APType)
import Pomc.Check (EncPrecFunc)
import Pomc.GStack(GStack)
import qualified Pomc.GStack as GS
import qualified Pomc.CustoMap as CM
import qualified Pomc.Prob.GReach as GR
import Pomc.Prob.SupportGraph(GraphNode(..), SupportGraph)
import Pomc.Prob.ProbEncoding(ProbEncodedSet)
import qualified Pomc.Prob.ProbEncoding as PE
import qualified Pomc.Encoding as E
import Pomc.Prob.FixPoint(VarKey)
import Pomc.Z3T

import  Data.Strict.IntMap(IntMap)
import Data.Map(Map)
import qualified Data.Strict.IntMap as StrictIntMap
import qualified Data.Strict.Map as StrictMap
import qualified Data.Map as Map

import Data.Set(Set)
import qualified Data.Set as Set
import Data.IntSet(IntSet)
import qualified Data.IntSet as IntSet

import Data.List(partition)
import Data.Vector(Vector, (!))
import qualified Data.Vector as V
import Data.Bifunctor(first)
import Data.Ratio ((%))

import Control.Monad.IO.Class (MonadIO(liftIO))
import Control.Monad (when, forM_, foldM, forM)
import Control.Monad.ST (ST, RealWorld)

import Data.STRef (STRef, newSTRef, readSTRef, modifySTRef')
import Data.Maybe (fromJust, isNothing, mapMaybe, catMaybes)

import GHC.Generics (Generic)
import Data.Hashable
import qualified Data.HashTable.IO as HT
import qualified Data.HashTable.ST.Basic as BH

import Z3.Monad

-- import qualified Debug.Trace as DBG
-- A data type for nodes in the augmented graph G
data GNode = GNode
  { gId        :: Int
  , graphNode  :: Int
  , phiNode    :: State
  , edges      :: Set HEdge
  -- -- needed for the SCC algorithm
  , iValue     :: Int
  , descSccs   :: IntSet
  } deriving Show

instance Eq GNode where
  p == q =  gId p ==  gId q

instance  Ord GNode where
  compare p q = compare ( gId p) ( gId q)

instance Hashable GNode where
  hashWithSalt salt s = hashWithSalt salt $ gId s

-- a basic open-addressing hashtable using linear probing
-- s = thread state, k = key, v = value.
type HashTable s k v = BH.HashTable s k v

-- a state in the cross product between the popa and the phiAutomaton
-- similar to MCState in the non probabilistic case
data AugState pstate =  AugState (StateId pstate) State deriving (Generic, Eq, Show, Ord)

instance Hashable (AugState state) where
  hashWithSalt salt (AugState sId phiState) = hashWithSalt salt $ pack phiState
    where
      pack WState{current = curr, pending = pend, stack = st, mustPush = mP, mustShift = mS, afterPop = aP} = (getId sId, curr, pend, st, mP, mS, aP)
      pack _ = error "state for finite-string model checking"

instance SatState (AugState s) where
  getSatState (AugState _ p) = p
  {-# INLINABLE getSatState #-}

  -- always promote the label
  getStateProps _ (AugState sId _ ) = getLabel sId
  {-# INLINABLE getStateProps #-}

-- a type for Graph G
type GGraph s = CM.CustoMap s GNode
type GraphNodesSCC = IntSet

data HEdge = Internal {probInt :: Prob, toG :: Int} |
  Support {toG :: Int, satSet :: ProbEncodedSet} |
  SupportAndInternal {probInt :: Prob, toG :: Int, satSet :: ProbEncodedSet}
  deriving Show

instance Eq HEdge where
  p == q = (toG p) == (toG q)

instance Ord HEdge where
  compare p q = compare (toG p) (toG q)

-- the global variables in the algorithm for constructing and analysing graph G
data GGlobals s pstate = GGlobals
  { idSeq      :: STRef s Int
  , ggraphMap   :: HashTable s (Int, State) Int
  , gGraph      :: STRef s (GGraph s)
  , grGlobals   :: GR.GRobals s (AugState pstate)
  , sStack     :: GStack s HEdge
  , bStack     :: GStack s Int
  , cGabow     :: STRef s Int
  -- bottom SCCs of subgraph H
  -- in qualitative model checking, we store only those reachable from an initial state where input formula phi does not hold
  , bottomHSCCs  :: STRef s (IntMap GraphNodesSCC)
  }

-- requires: the initial semiconfiguration has id 0, and it is not reachable from itself
-- pstate: a parametric type for states of the input popa
qualitativeModelCheck :: (MonadIO m, MonadLogger m, Ord pstate, Hashable pstate, Show pstate)
  => DeltaWrapper pstate
  -> Formula APType -- phi: input formula to check
  -> [State] -- initial states of the phiOpa 
  -> SupportGraph pstate
  -> StrictMap.Map pstate Int
  -> Vector Bool
  -> STRef RealWorld Stats
  -> m Bool
qualitativeModelCheck delta phi phiInitials suppGraph sIdMap pendVector stats = do
  -- global data structures for constructing graph G and for qualitative model checking
  gGlobals <- liftSTtoIO $ do
    let numPendingSemiconfs = foldl (flip ((+) . fromEnum)) 0 pendVector
    newIdSequence <- newSTRef (0 :: Int)
    emptyGGraphMap <- BH.newSized numPendingSemiconfs
    emptyGGraph <- CM.emptySized numPendingSemiconfs
    emptyGRGlobals <- GR.newGRobals
    -- -1 is reserved for trivial (that is, single node that does not depend on itself) SCCs
    sccCounter <- newSTRef (-2 :: Int)
    newSS         <- GS.new
    newBS         <- GS.new
    newFoundSCCs <- newSTRef StrictIntMap.empty
    return GGlobals { idSeq = newIdSequence
                    , ggraphMap = emptyGGraphMap
                    , gGraph = emptyGGraph
                    , grGlobals = emptyGRGlobals
                    , sStack = newSS
                    , bStack = newBS
                    , cGabow = sccCounter
                    , bottomHSCCs = newFoundSCCs
                    }

  logInfoN "Building and Analyzing graph G..."
  let iniGn = suppGraph ! 0
      iniLabel = getLabel . fst . semiconf $ iniGn
      isPhiState = E.member (bitenc delta) phi . current
      phiInitialsFilter s = iniLabel == E.extractInput (bitenc delta) (current s)
      (phiStates, notPhiStates) = partition isPhiState . filter phiInitialsFilter $ phiInitials

    -- explore nodes where phi does NOT hold
  liftSTtoIO $ forM_ notPhiStates $ \s -> do
      -- create a new GNode 
    newId <- freshPosId (idSeq gGlobals)
    BH.insert (ggraphMap gGlobals) (gnId iniGn, s) newId
    let node =
          GNode {gId= newId, graphNode = gnId iniGn, phiNode = s, edges = Set.empty, iValue = 0, descSccs = IntSet.empty}
    CM.insert (gGraph gGlobals) newId node
    addtoPath gGlobals node (Internal 0 newId) >>= dfs suppGraph gGlobals delta (pendVector V.!) False sIdMap

  -- explore nodes where phi holds
  forM_ phiStates $ \s -> do
    nullCandidates <- StrictIntMap.null <$> liftSTtoIO (readSTRef (bottomHSCCs gGlobals))
    if nullCandidates
      then logInfoN "Skipping exploring a portion of graph G because there are no bottom SCCs reachable from notPhi initial states"
      else liftSTtoIO $ do
      -- create a new GNode 
      newId <- freshPosId (idSeq gGlobals)
      BH.insert (ggraphMap gGlobals) (gnId iniGn, s) newId
      let node = GNode {gId= newId, graphNode = gnId iniGn, phiNode = s, edges = Set.empty, iValue = 0, descSccs = IntSet.empty}
      CM.insert (gGraph gGlobals) newId node
      addtoPath gGlobals node (Internal 0 newId) >>= dfs suppGraph gGlobals delta (pendVector V.!) True sIdMap >> return ()

  -- some statistics about graph G
  idx <- liftSTtoIO $ readSTRef . idSeq $ gGlobals
  logInfoN $ "(The relevant portion of) Graph G has " ++ show idx ++ " nodes."
  liftSTtoIO $ modifySTRef' stats (\s -> s {gGraphSize = idx})

  -- returning whether there is a bottom SCC in H reachable from a not Phi initial node
  StrictIntMap.null <$> liftSTtoIO (readSTRef (bottomHSCCs gGlobals))


reachPush :: (Ord pstate, Hashable pstate, Show pstate)
  => GGlobals s pstate -- global variables of the algorithm
  -> DeltaWrapper pstate
  -> SupportGraph pstate
  -> Bool
  -> (Int -> Bool) -- is a semiconf pending?
  -> StrictMap.Map pstate Int
  -> (GraphNode pstate, State) -- current gnode
  -> ST s IntSet
reachPush gGlobals delta suppGraph fromPhi isPending sIdMap (gn, p) =
  let fPushGns = map (first (suppGraph !)) . filter (isPending . fst) . StrictIntMap.toList $ internalEdges gn
      fSuppGns = map (suppGraph !) . filter isPending . IntSet.toList $ supportEdges gn
      fPushPhiStates = (phiDeltaPush delta) p
      currentInput q = E.extractInput (bitenc delta) (current q)
      fPushGnodes =
        [(prob_, gn1, p1) |
            (gn1, prob_) <- fPushGns, p1 <- fPushPhiStates
          , (getLabel . fst . semiconf $ gn1) == currentInput p1
        ]
      -- for exploring supports
      precRel = (prec delta)
      leftContext = AugState (fst . semiconf $ gn) p
      cDeltaPush (AugState (StateId _ q0 lab0) p0)  =
        [(AugState (StateId id1 q1 lab1) p1, prob_) |
            (q1, lab1, prob_) <- (deltaPush delta) q0
          , p1 <- (phiDeltaPush delta) p0
          , (precRel lab0 lab1 == Just Take) || lab1 == currentInput p1
          , let id1 = sIdMap StrictMap.! q1
        ]
      cDeltaShift (AugState (StateId _ q0 lab0) p0) =
        [ (AugState (StateId id1 q1 lab1) p1, prob_) |
            (q1, lab1, prob_) <- (deltaShift delta) q0
          , p1 <- (phiDeltaShift delta) p0
          , (precRel lab0 lab1 == Just Take) || lab1 == currentInput p1
          , let id1 = sIdMap StrictMap.! q1
        ]
      cDeltaPop (AugState (StateId _ q0 _) p0) (AugState (StateId _ q1 _) p1)  =
        [(AugState (StateId id2 q2 lab2) p2, prob_) |
            (q2, lab2, prob_) <- (deltaPop delta) q0 q1
          , let id2 = sIdMap StrictMap.! q2
          , p2 <- (phiDeltaPop delta) p0 p1
        ]

      consistentFilter (AugState sId0 p0) = (getLabel sId0) == currentInput p0
      cDelta = GR.Delta
        { GR.bitenc = bitenc delta
        , GR.proBitenc = proBitenc delta
        , GR.prec   = prec delta
        , GR.deltaPush = cDeltaPush
        , GR.deltaShift = cDeltaShift
        , GR.deltaPop = cDeltaPop
        , GR.consistentFilter = consistentFilter
        }
  in do
    fromId <- fromJust <$> BH.lookup (ggraphMap gGlobals) (gnId gn, p)
    -- handling support edges
    fSuppAugStates <- if not . null $ fSuppGns
                        then GR.reachableStates (grGlobals gGlobals) cDelta leftContext
                        else return []
    -- a sanity check
    -- unless (all (consistentFilter. fst) fSuppAugStates) $ error "a support Augmented State is inconsistent"
    let fSuppGnodes =
          [(gn1, p1, suppSatSet) |
            gn1 <- fSuppGns
            , (AugState (StateId _ q _) p1, suppSatSet) <- fSuppAugStates
            , (getState . fst . semiconf $ gn1) == q
          ]
    -- exploring edges
    reachEdges gGlobals delta suppGraph fromPhi isPending sIdMap fromId fPushGnodes fSuppGnodes


reachShift :: (Ord pstate, Hashable pstate, Show pstate)
  => GGlobals s pstate -- global variables of the algorithm
  -> DeltaWrapper pstate
  -> SupportGraph pstate
  -> Bool
  -> (Int -> Bool) -- is a semiconf pending?
  -> StrictMap.Map pstate Int
  -> (GraphNode pstate, State) -- current GNopde
  -> ST s IntSet
reachShift gGlobals delta suppGraph fromPhi isPending sIdMap (gn, p) =
  let fGns = map (first (suppGraph !)) . filter (isPending . fst) . StrictIntMap.toList $ internalEdges gn
      fPhiStates = (phiDeltaShift delta) p
      fGnodes =
        [(prob_, gn1, p1) |
          (gn1, prob_) <- fGns, p1 <- fPhiStates,
          (getLabel . fst . semiconf $ gn1) == E.extractInput (bitenc delta) (current p1)
        ]
  in do
    fromId <- fromJust <$> BH.lookup (ggraphMap gGlobals) (gnId gn, p)
    reachEdges gGlobals delta suppGraph fromPhi isPending sIdMap fromId fGnodes []

reachEdges :: (Ord pstate, Hashable pstate, Show pstate)
  => GGlobals s pstate -- global variables of the algorithm
  -> DeltaWrapper pstate
  -> SupportGraph pstate
  -> Bool
  -> (Int -> Bool) -- is a semiconf pending?
  -> StrictMap.Map pstate Int
  -> Int -- id of current node
  -> [(Prob, GraphNode pstate, State)] -- internal(push/shift) edges
  -> [(GraphNode pstate, State, ProbEncodedSet)] -- support edges
  -> ST s IntSet
reachEdges gGlobals delta suppGraph fromPhi isPending sIdMap fromId intDests suppDests =
  let mergeEd (Internal p to1_) (Support _ suppSatSet) = SupportAndInternal p to1_ suppSatSet
      mergeEd (Support _ suppSatSet) (Internal p to1_)  = SupportAndInternal p to1_ suppSatSet
      mergeEd _ _ = error "This merge is not allowed - please report this as a bug."

      computeId gn p = do
        maybeId <- BH.lookup (ggraphMap gGlobals) (gnId gn, p)
        actualId <- maybe (freshPosId $ idSeq gGlobals) return maybeId
        when (isNothing maybeId) $ do
            BH.insert (ggraphMap gGlobals) (gnId gn, p) actualId
            CM.insert (gGraph gGlobals) actualId
              $ GNode {gId= actualId, graphNode = gnId gn, phiNode = p, edges = Set.empty, iValue = 0, descSccs = IntSet.empty}
        return actualId
  in do
    intEs <- StrictIntMap.fromList <$> forM intDests ( \(prob_, gn1, p1) -> do
      actualId <- computeId gn1 p1
      return (actualId, Internal prob_ actualId))

    allEs <- foldM (\acc (gn1,p1, suppSatSet) -> do
        actualId <- computeId gn1 p1
        return (StrictIntMap.insertWith mergeEd actualId (Support actualId suppSatSet) acc)
      ) intEs suppDests

    let edges_ = StrictIntMap.elems allEs
    CM.modify (gGraph gGlobals) (\g -> g{edges = Set.fromAscList edges_}) fromId
    IntSet.unions <$> forM edges_ ( \e -> do
      nextNode <- CM.lookup (gGraph gGlobals) (toG e)
      let cases
            | iValue nextNode == 0 = addtoPath gGlobals nextNode e >>= dfs suppGraph gGlobals delta isPending fromPhi sIdMap
            | iValue nextNode < 0  = return (descSccs nextNode)
            -- I need to push anyway because I want to keep track of cycles in createComponent
            | iValue nextNode > 0  = GS.push (sStack gGlobals) e >> merge gGlobals nextNode >> return IntSet.empty
            | otherwise = error "unreachable error"
      cases)

dfs :: (Ord pstate, Hashable pstate, Show pstate)
  => SupportGraph pstate
  -> GGlobals s pstate
  -> DeltaWrapper pstate
  -> (Int -> Bool) -- is a semiconf pending?
  -> Bool
  -> StrictMap.Map pstate Int
  -> GNode
  -> ST s IntSet
dfs suppGraph gGlobals delta isPending fromPhi sIdMap gnode =
  let gn = suppGraph ! (graphNode gnode)
      p = phiNode gnode
      (q,g) = semiconf gn
      precRel = (prec delta) (fst . fromJust $ g) (getLabel q)
      buildCases
        -- a sanity check
        -- | getLabel q /= E.extractInput (bitenc delta) (current p) = 
            -- error "inconsistent GNode when analyzing graph G for qualitative mc"

        -- this case includes the initial push
        | (isNothing g) || precRel == Just Yield =
            reachPush gGlobals delta suppGraph fromPhi isPending sIdMap (gn,p)

        | precRel == Just Equal =
            reachShift gGlobals delta suppGraph fromPhi isPending sIdMap (gn, p)

        | precRel == Just Take = error
          $ "a pop transition cannot be reached in the augmented graph of pending semiconfs, as it terminates almost surely" ++ show gn

        | otherwise = return IntSet.empty
  in do
    descendantSCCs <- buildCases
    if fromPhi
      then createComponentPhi gGlobals gnode descendantSCCs
      else createComponent suppGraph gGlobals delta isPending gnode descendantSCCs


createComponent :: SupportGraph pstate -> GGlobals s pstate -> DeltaWrapper pstate -> (Int -> Bool) -> GNode -> IntSet -> ST s IntSet
createComponent suppGraph gGlobals delta isPending g descendantSCCs = do
  topB <- GS.peek $ bStack gGlobals
  if (iValue g) == topB
    then do
      GS.pop_ (bStack gGlobals)
      sSize <- GS.size $ sStack gGlobals
      poppedEdges <- GS.multPop (sStack gGlobals) (sSize - (iValue g) + 1) -- the last one is to gn
      if length poppedEdges == 1
        then do
          CM.modify (gGraph gGlobals) (\g -> g{iValue = -1, descSccs = descendantSCCs}) (gId g)
          return descendantSCCs
        else do
          -- discard all descendants that share a semiconf with the current one
          let sccEdges = init poppedEdges
          sccSemiconfs <- IntSet.fromList <$> forM sccEdges (\e -> graphNode <$> CM.lookup (gGraph gGlobals) (toG e))
          filteredDescendants <- deleteDescendants gGlobals sccSemiconfs descendantSCCs
          -- check if current SCC is a candidate bottom SCC of H
          let isBott = isBottom suppGraph sccSemiconfs isPending
          isAccept <- isAccepting gGlobals delta sccEdges
          if isBott && isAccept
            then do
              newSCCid <- freshNegId (cGabow gGlobals)
              modifySTRef' (bottomHSCCs gGlobals) $ StrictIntMap.insert newSCCid sccSemiconfs
              let descs = IntSet.insert newSCCid filteredDescendants
              forM_ sccEdges $ \e -> CM.modify (gGraph gGlobals) (\g -> g{iValue = newSCCid, descSccs = descs}) (toG e)
              return descs
            else do
              forM_ sccEdges $ \e -> CM.modify (gGraph gGlobals) (\g -> g{iValue = -1, descSccs = filteredDescendants}) (toG e)
              return filteredDescendants
    else return descendantSCCs

createComponentPhi :: GGlobals s pstate -> GNode -> IntSet -> ST s IntSet
createComponentPhi gGlobals g descendantSCCs = do
  topB <- GS.peek $ bStack gGlobals
  if (iValue g) == topB
    then do
      GS.pop_ (bStack gGlobals)
      sSize <- GS.size $ sStack gGlobals
      sccEdges <- GS.multPop (sStack gGlobals) (sSize - (iValue g) + 1) -- the last one is to gn
      if length sccEdges == 1
        then do
          CM.modify (gGraph gGlobals) (\g -> g{iValue = -1, descSccs = descendantSCCs}) (gId g)
          return descendantSCCs
        else do
          -- discard all descendants that share a semiconf with the current one
          sccSemiconfs <- IntSet.fromList <$> forM sccEdges (\e -> graphNode <$> CM.lookup (gGraph gGlobals) (toG e))
          filteredDescendants <- deleteDescendants gGlobals sccSemiconfs descendantSCCs
          forM_ sccEdges $ \e -> CM.modify (gGraph gGlobals) (\g -> g{iValue = -1, descSccs = filteredDescendants}) (toG e)
          return filteredDescendants
    else return descendantSCCs

-- Gabow helpers
addtoPath :: GGlobals s pstate -> GNode -> HEdge -> ST s GNode
addtoPath gGlobals node edge  = do
  GS.push (sStack gGlobals) edge
  sSize <- GS.size $ sStack gGlobals
  CM.modify (gGraph gGlobals) (\g -> g{iValue = sSize}) (gId node)
  GS.push (bStack gGlobals) sSize
  return node{iValue = sSize}

-- contract the B stack, that represents the boundaries between SCCs on the current path
merge :: GGlobals s pstate -> GNode -> ST s ()
merge gGlobals g = GS.popWhile_ (bStack gGlobals) (\x -> iValue g < x)
-- end Gabow helpers

-- helpers for the construction of subgraph H
--
deleteDescendants :: GGlobals s pstate -> GraphNodesSCC -> IntSet -> ST s IntSet
deleteDescendants gGlobals sccSemiconfs descendants = do
  modifySTRef' (bottomHSCCs gGlobals) $
    StrictIntMap.filterWithKey (\idx scc -> not (IntSet.member idx descendants) || IntSet.disjoint sccSemiconfs scc)
  -- returning filtered descendants
  (\m -> IntSet.filter (`StrictIntMap.member` m) descendants) <$> readSTRef (bottomHSCCs gGlobals)

-- first necessary condition for an SCC of G to be a BSCC of H from [Etessami and Yannakakis, TOCL 2012, Theo 30]
isBottom :: SupportGraph pstate -> IntSet -> (Int -> Bool) -> Bool
isBottom suppGraph suppGraphSCC isPending =
  let gns = map (suppGraph !) (IntSet.toList suppGraphSCC)
      bottomCheck = all (`IntSet.member` suppGraphSCC) . filter isPending
  in all (\gn -> (bottomCheck . StrictIntMap.keys . internalEdges) gn && (bottomCheck . IntSet.elems . supportEdges) gn) gns

-- third necessary condition for an SCC of G to be a BSCC of H from [Etessami and Yannakakis, TOCL 2012, Theo 30]
isAccepting :: GGlobals s pstate -> DeltaWrapper pstate -> [HEdge] -> ST s Bool
isAccepting gGlobals delta sccEdges = do
  gs <- mapM (CM.lookup (gGraph gGlobals) . toG) sccEdges
  let maybeSupport (Internal _ _) = Nothing
      maybeSupport (Support _ sss) = Just sss
      maybeSupport (SupportAndInternal _ _ sss) = Just sss
      acceptanceBitVector = PE.unions $ map (PE.encodeSatState (proBitenc delta) . phiNode) gs ++ mapMaybe maybeSupport sccEdges
  return $ PE.isSatisfying acceptanceBitVector

-- condition (2) from [Etessami and Yannakakis, TOCL 2012, Theo 30] is checked via the topological decomposition
--
-- end helpers for the construction of subgraph H

-- quantitative model checking --
-- requires: the initial semiconfiguration has id 0, and it is not reachable from itself
-- pstate: a parametric type for states of the input popa
quantitativeModelCheck :: (MonadIO m, MonadFail m, MonadLogger m, Ord pstate, Hashable pstate, Show pstate)
  => DeltaWrapper pstate
  -> Formula APType -- phi: input formula to check
  -> [State] -- initial states of the phiOpa
  -> SupportGraph pstate
  -> Vector Bool
  -> Map VarKey Prob
  -> Map VarKey Prob
  -> StrictMap.Map pstate Int
  -> STRef RealWorld Stats
  -> Pomc.Prob.ProbUtils.Solver
  -> m (Prob, Prob)
quantitativeModelCheck delta phi phiInitials suppGraph pendVector lowerBounds upperBounds sIdMap stats solv = do
  startGGTime <- startTimer

  -- globals data structures for qualitative model checking
  -- -1 is reserved for useless (i.e. single node) SCCs
  gGlobals <- liftSTtoIO $ do
    newIdSequence <- newSTRef (0 :: Int)
    let numPendingSemiconfs = foldl (flip ((+) . fromEnum)) 0 pendVector
    emptyGGraphMap <- BH.newSized numPendingSemiconfs
    emptyGGraph <- CM.emptySized numPendingSemiconfs
    emptyGRGlobals <- GR.newGRobals
    sccCounter   <- newSTRef (-2 :: Int)
    newSS        <- GS.new
    newBS        <- GS.new
    newFoundSCCs <- newSTRef StrictIntMap.empty
    return GGlobals { idSeq = newIdSequence
                    , ggraphMap = emptyGGraphMap
                    , gGraph = emptyGGraph
                    , grGlobals = emptyGRGlobals
                    , sStack = newSS
                    , bStack = newBS
                    , cGabow = sccCounter
                    , bottomHSCCs = newFoundSCCs
                    }
  logInfoN "Building and Analyzing graph G..."
  let iniGn = suppGraph ! 0
      iniLabel = getLabel . fst . semiconf $ iniGn
      isPhiState = E.member (bitenc delta) phi . current
      phiInitialsFilter s = iniLabel == E.extractInput (bitenc delta) (current s)
      initialStates = filter phiInitialsFilter phiInitials

  phiInitialGNodesIdxs <- catMaybes <$> forM initialStates (\s -> liftSTtoIO $ do
      -- create a new GNode 
    newId <-  freshPosId (idSeq gGlobals)
    BH.insert (ggraphMap gGlobals) (gnId iniGn, s) newId
    let node = GNode {gId= newId, graphNode = gnId iniGn, phiNode = s, edges = Set.empty, iValue = 0, descSccs = IntSet.empty}
    CM.insert (gGraph gGlobals) newId node
    -- we always set fromPhi to False because we want to keep track of ALL BSCCs of subgraph H, contrarily to qualitative mc.
    addtoPath gGlobals node (Internal 0 newId) >>= dfs suppGraph gGlobals delta (pendVector V.!) False sIdMap >> return ()
    if isPhiState s
      then return (Just newId)
      else return Nothing)

  hSCCs <- liftSTtoIO $ StrictIntMap.keysSet <$> readSTRef (bottomHSCCs gGlobals)

  -- some statistics about graph G
  logInfoN "Computed qualitative model checking..."
  tGG <- stopTimer startGGTime hSCCs
  liftSTtoIO $ modifySTRef' stats (\s -> s {gGraphTime = tGG })
  idx <- liftSTtoIO . readSTRef . idSeq $ gGlobals
  g <- CM.take idx <$> liftSTtoIO (readSTRef (gGraph gGlobals))
  freezedGGraph <- liftSTtoIO $ V.freeze g
  liftSTtoIO $ modifySTRef' stats (\s -> s {gGraphSize = idx})
  logInfoN $ "Graph G has " ++ show idx ++ " nodes."

  -- bottomString <- show <$> readSTRef (bottomHSCCs gGlobals)
  -- gString <- CM.showMap computedGraph
  -- logDebugN gString
  -- logDebugN bottomString

  -- computing the probability of satisfying the temporal formula
  let isInH = not . IntSet.null . IntSet.intersection hSCCs . descSccs
      genPendProbs bounds = V.generate (V.length suppGraph) (\idx -> 1 - StrictIntMap.findWithDefault 0 idx boundsMap)
        where boundsMap = StrictIntMap.fromListWith (+) . map (first fst) . Map.toList $ bounds

      pendProbsUpperBounds = genPendProbs lowerBounds
      pendProbsLowerBounds = genPendProbs upperBounds

      insert var Nothing         = (Just [var], ())
      insert var (Just old_vars) = (Just (var:old_vars), ())

  evalZ3TWith (Just QF_LRA) stdOpts $ do
    -- generate all variables and add them to two hashtables
    newlMap <- liftSTtoIO BH.new
    newlGroupedMap <- liftSTtoIO BH.new
    newuMap <- liftSTtoIO BH.new
    newuGroupedMap <- liftSTtoIO BH.new
    forM_ freezedGGraph $ \g -> when (isInH g) $ do
      newlVar <- mkFreshRealVar (show (gId g) ++ "L")
      newuVar <- mkFreshRealVar (show (gId g) ++ "U")
      liftIO $ HT.insert newlMap (gId g) newlVar
      liftIO $ HT.insert newuMap (gId g) newuVar
      liftIO $ HT.mutate newlGroupedMap (graphNode g) (insert newlVar)
      liftIO $ HT.mutate newuGroupedMap (graphNode g) (insert newuVar)

    logInfoN "Generated z3 vars for encoding (2) from [Etessami and Yannakakis, TOCL 2012,Lemmas 34 and 35]"

    -- preparing the global variables for the computation of the fractions f
    freezedSuppEnds <- liftIO $ GR.freezeSuppEnds (grGlobals gGlobals)
    freezedSuppStarts <- liftIO $ GR.freezeSuppStarts (grGlobals gGlobals)

    lenHashtables <- liftSTtoIO $ GR.nrSemiconfs (grGlobals gGlobals)
    globals <- GR.newWeightedGRobals lenHashtables stats

    logInfoN "Encoding conditions (2b) and (2c) from [Etessami and Yannakakis, TOCL 2012,Lemmas 34 and 35]"
    -- encodings (2b) and (2c)
    encs1 <- concat <$> mapM
      (\gNode -> encode
          globals (GR.sIdGen (grGlobals gGlobals)) freezedSuppStarts freezedSuppEnds delta
          (newlMap, newuMap) suppGraph freezedGGraph (prec delta) isInH gNode
          pendProbsLowerBounds pendProbsUpperBounds sIdMap (useNewton solv)
      ) (V.filter isInH freezedGGraph)

    logInfoN "Encoding conditions (2a) from [Etessami and Yannakakis, TOCL 2012,Lemmas 34 and 35]"
    -- encoding (2a) for lower bounds
    groupedlMaptoList <- liftIO (HT.toList newlGroupedMap)
    encs2 <- foldM (\acc (_, vList) -> do
        vSum <- mkAdd vList
        lConstr1 <- mkLe vSum =<< mkRational (1 :: Prob)
        lConstr2 <- mkGe vSum =<< mkRational (1 - 1 % 100)
        eqString <- astToString lConstr1
        logInfoN $ "Asserting Sum equal 1: " ++ eqString
        return (lConstr1:lConstr2:acc)
      ) [] groupedlMaptoList

    -- encoding (2a) for upper bounds
    groupeduMaptoList <- liftIO (HT.toList newuGroupedMap)
    encs3 <- foldM (\acc (_, vList) -> do
      vSum <- mkAdd vList
      uConstr1 <- mkGe vSum =<< mkRational (1 :: Prob)
      eqString <- astToString uConstr1
      logInfoN $ "Asserting Sum equal 1: " ++ eqString
      uConstr2 <- mkLe vSum =<< mkRational (1 + 1 % 100)
      eqString <- astToString uConstr2
      logInfoN $ "Asserting Sum equal 1: " ++ eqString
      return (uConstr1:uConstr2:acc)
      ) [] groupeduMaptoList

    -- computing bounds on the probability to satisfy the given property
    let phiInitialGNodesIdxsinH = filter (isInH . (freezedGGraph V.!)) phiInitialGNodesIdxs
    philVars <- liftIO $ mapM  (fmap fromJust . HT.lookup newlMap) phiInitialGNodesIdxsinH
    phiuVars <- liftIO $ mapM  (fmap fromJust . HT.lookup newuMap) phiInitialGNodesIdxsinH

    sumlVar <- mkAdd philVars
    eqStringL <- astToString sumlVar
    logInfoN $ "Sum of interest (lower bound): " ++ eqStringL
    sumuVar <- mkAdd phiuVars
    eqStringU <- astToString sumuVar
    logInfoN $ "Sum of interest (upper bound): " ++ eqStringU

    startSol <- startTimer
    mapM_ assert encs1 >> mapM_ assert encs2 >> mapM_ assert encs3
    logInfoN "Calling Z3 to solve the linear program for quantitative model checking..."
    let parseResult (Sat, bounds) = fromJust bounds
        parseResult _ = error "the linear program for quantitative model checking has no solution."
    (lb, ub) <- parseResult <$> withModel (\model -> do
      l <- extractLowerProb . fromJust =<< eval model sumlVar
      u <- extractUpperProb . fromJust =<< eval model sumuVar
      logInfoN $ "Computed lower bound on the quantitative probability: " ++ show l
      logInfoN $ "Computed upper bound on the quantitative probability: " ++ show u
      return (l, u))

    tSol <- stopTimer startSol ub
    liftSTtoIO $ modifySTRef' stats (\s -> s { quantSolTime = quantSolTime s + tSol})
    return (lb, min 1 ub)

-- helpers for the Z3 encoding
-- every node of graph H is associated with a Z3 var
type TypicalVarMap = HT.BasicHashTable Int AST

encodeTransition :: MonadZ3 z3 => Prob -> Prob -> Prob -> AST -> z3 AST
encodeTransition prob_ num den toVar = do
  rtNum <- mkRational num
  rtProb_ <- mkRational prob_
  rtDen <- mkRational den
  mul <- mkMul $ rtProb_:rtNum:[toVar]
  mkDiv mul rtDen

encode :: (MonadZ3 z3, MonadFail z3, MonadLogger z3, Ord pstate, Hashable pstate, Show pstate)
      => GR.WeightedGRobals (AugState pstate)
      -> SIdGen RealWorld (AugState pstate)
      -> Vector [SU.Stack (AugState pstate)]
      -> Vector (Vector (SU.StateId (AugState pstate)))
      -> DeltaWrapper pstate
      -> (TypicalVarMap, TypicalVarMap)
      -> SupportGraph pstate
      -> Vector GNode
      -> EncPrecFunc
      -> (GNode -> Bool)
      -> GNode
      -> Vector Prob
      -> Vector Prob
      -> StrictMap.Map pstate Int
      -> Bool
      -> z3 [AST]
encode wGrobals sIdGen suppStarts supports delta (lTypVarMap, uTypVarMap) suppGraph gGraph precFun isInH gNode pendProbsLB pendProbsUB sIdMap useNewton =
  let gn = suppGraph ! graphNode gNode
      (q,g) = semiconf gn
      qLabel = getLabel q
      precRel = precFun (fst . fromJust $ g) qLabel -- safe due to laziness
      cases
        -- this case includes the initial push
        | isNothing g || precRel == Just Yield =
            encodePush wGrobals sIdGen suppStarts supports delta (lTypVarMap, uTypVarMap) suppGraph
              gGraph isInH gNode gn pendProbsLB pendProbsUB sIdMap useNewton

        | precRel == Just Equal =
            encodeShift (lTypVarMap, uTypVarMap) gGraph isInH gNode pendProbsLB pendProbsUB

        | otherwise = fail "unexpected prec rel"
   in cases

-- encoding helpers --
encodePush :: (MonadZ3 z3, MonadFail z3, MonadLogger z3, Ord pstate, Hashable pstate, Show pstate)
  => GR.WeightedGRobals (AugState pstate)
  -> SIdGen RealWorld (AugState pstate)
  -> Vector [SU.Stack (AugState pstate)]
  -> Vector (Vector(SU.StateId (AugState pstate)))
  -> DeltaWrapper pstate
  -> (TypicalVarMap, TypicalVarMap)
  -> SupportGraph pstate
  -> Vector GNode
  -> (GNode -> Bool)
  -> GNode
  -> GraphNode pstate
  -> Vector Prob
  -> Vector Prob
  -> StrictMap.Map pstate Int
  -> Bool
  -> z3 [AST]
encodePush wGrobals sIdGen suppStarts supports delta (lTypVarMap, uTypVarMap) suppGraph gGraph isInH g gn pendProbsLB pendProbsUB sIdMap useNewton =
  let edgesInH = Set.toList . Set.filter (isInH . (gGraph V.!). toG) . edges $ g
      trivialSCC [] = error "there must be at least one edge in H"
      trivialSCC [e] = (toG e) == (gId g)
      trivialSCC _ = False

      pushEnc e = do
        let toIdx = toG e
        tolVar <- liftIO $ fromJust <$> HT.lookup lTypVarMap toIdx
        touVar <- liftIO $ fromJust <$> HT.lookup uTypVarMap toIdx
        let destG = gGraph ! toIdx
            -- push edges in the support Graph
            encodePushTrans = do
              lT <- encodeTransition (probInt e) (pendProbsLB ! (graphNode destG)) (pendProbsUB V.! (graphNode g)) tolVar
              uT <- encodeTransition (probInt e) (pendProbsUB ! (graphNode destG)) (pendProbsLB V.! (graphNode g)) touVar
              return [(lT, uT)]
            -- supports edges in the Support Graph
            supportGn = suppGraph V.! (graphNode destG)
            -- augmented states in the cross product
            leftContext = AugState (fst . semiconf $ gn) (phiNode g)
            rightContext = AugState (fst . semiconf $ supportGn) (phiNode destG)
            precRel = prec delta
            currentInput q = E.extractInput (bitenc delta) (current q)
            cDeltaPush (AugState (StateId _ q0 lab0) p0) =
              [ (AugState (StateId id1 q1 lab1) p1, prob_) |
                  (q1, lab1, prob_) <- (deltaPush delta) q0
                , p1 <- (phiDeltaPush delta) p0
                , (precRel lab0 lab1 == Just Take) || lab1 == currentInput p1
                , let id1 = sIdMap StrictMap.! q1
              ]
            cDeltaShift (AugState (StateId _ q0 lab0) p0) =
              [ (AugState (StateId id1 q1 lab1) p1, prob_) |
                  (q1, lab1, prob_) <- (deltaShift delta) q0
                , p1 <- (phiDeltaShift delta) p0
                , (precRel lab0 lab1 == Just Take) || lab1 == currentInput p1
                , let id1 = sIdMap StrictMap.! q1
              ]
            cDeltaPop (AugState (StateId _ q0 _) p0) (AugState (StateId _ q1 _) p1)  =
              [(AugState (StateId id2 q2 lab2) p2, prob_) |
                  (q2, lab2, prob_) <- (deltaPop delta) q0 q1
                ,  let id2 = sIdMap StrictMap.! q2
                ,  p2 <- (phiDeltaPop delta) p0 p1
              ]

            consistentFilter (AugState sId p0) = (getLabel sId) == currentInput p0
            cDelta = GR.Delta
              { GR.bitenc = bitenc delta
              , GR.proBitenc = proBitenc delta
              , GR.prec   = prec delta
              , GR.deltaPush = cDeltaPush
              , GR.deltaShift = cDeltaShift
              , GR.deltaPop = cDeltaPop
              , GR.consistentFilter = consistentFilter
              }
            encodeSupportTrans = do
              logInfoN $ "encountered a support transition - launching call to inner computation of fraction f from H node "
                ++ show (gId g) ++ " to H node " ++ show toIdx
              (lW, uW) <- GR.weightQuerySCC wGrobals sIdGen cDelta suppStarts supports leftContext rightContext useNewton
              lT <- encodeTransition (lW) (pendProbsLB V.! (graphNode destG)) (pendProbsUB V.! (graphNode g)) tolVar
              uT <- encodeTransition (uW) (pendProbsUB V.! (graphNode destG)) (pendProbsLB V.! (graphNode g)) touVar
              return [(lT, uT)]
            cases
              | (SupportAndInternal {}) <- e = do
                  pushEncs <- encodePushTrans
                  suppEncs <- encodeSupportTrans
                  return (pushEncs ++ suppEncs)
              | (Internal _ _) <- e = encodePushTrans
              | (Support _ _) <- e = encodeSupportTrans
        cases
  in do
    -- a sanity check
    --unless (graphNode g == gnId gn) $ error "encodePush corresponding to non consistent pair GNode - graphNode"
    lvar <- liftIO $ fromJust <$> HT.lookup lTypVarMap (gId g)
    uvar <- liftIO $ fromJust <$> HT.lookup uTypVarMap (gId g)
    if trivialSCC edgesInH
      then do
        -- this would give an equation x = x, which has necessarily solution 1,
        -- otherwise it would violate uniqueness of solution
        -- this constraint is helpful to deal with bounds and approximations
        lEqOne <- mkEq lvar =<< mkRational (1 :: Prob)
        uEqOne <- mkEq uvar =<< mkRational (1 :: Prob)
        return [lEqOne, uEqOne]
      else do
        transitions <- concat <$> mapM pushEnc edgesInH
        lEq <- mkGe lvar =<< mkAdd (map fst transitions)
        uEq <- mkLe uvar =<< mkAdd (map snd transitions)
        soundness <- mkLe lvar uvar
        -- debugging
        eqLString <- astToString lEq
        logInfoN $ "Asserting Push/Support equation (lower bound): " ++ eqLString
        eqUString <- astToString uEq
        logInfoN $ "Asserting Push/Support equation (upper bound): " ++ eqUString
        return [lEq, uEq, soundness]


encodeShift :: (MonadZ3 z3, MonadLogger z3)
            => (TypicalVarMap, TypicalVarMap)
            -> Vector GNode
            -> (GNode -> Bool)
            -> GNode
            -> Vector Prob
            -> Vector Prob
            -> z3 [AST]
encodeShift (lTypVarMap, uTypVarMap) gGraph isInH g pendProbsLB pendProbsUB =
  let edgesInH = Set.toList . Set.filter (isInH . (gGraph V.!). toG) . edges $ g
      trivialSCC [] = error "there must be at least one edge in H"
      trivialSCC [e] = toG e == gId g
      trivialSCC _ = False
      shiftEnc (Internal prob_ toIdx) = do
        tolVar <- liftIO $ fromJust <$> HT.lookup lTypVarMap toIdx
        touVar <- liftIO $ fromJust <$> HT.lookup uTypVarMap toIdx
        let destG = gGraph V.! toIdx
        lT <- encodeTransition (prob_) (pendProbsLB V.! (graphNode destG)) (pendProbsUB V.! (graphNode g)) tolVar
        uT <- encodeTransition (prob_) (pendProbsUB V.! (graphNode destG)) (pendProbsLB V.! (graphNode g)) touVar
        return (lT, uT)

  in do
  -- a sanity check
  --unless (graphNode g == gnId gn) $ error "encodeShift encountered a non consistent pair GNode - graphNode"
  lvar <- liftIO $ fromJust <$> HT.lookup lTypVarMap (gId g)
  uvar <- liftIO $ fromJust <$> HT.lookup uTypVarMap (gId g)
  if trivialSCC edgesInH
    then do
      lEqOne <- mkEq lvar =<< mkRational (1 :: Prob)
      uEqOne <- mkEq uvar =<< mkRational (1 :: Prob)
      return [lEqOne, uEqOne]
    else do
      transitions <- mapM shiftEnc edgesInH
      lEq <- mkGe lvar =<< mkAdd (map fst transitions)
      uEq <- mkLe uvar =<< mkAdd (map snd transitions)
      soundness <- mkLe lvar uvar
      -- debugging
      eqLString <- astToString lEq
      logInfoN $ "Asserting Shift equation (lower bound): " ++ eqLString
      eqUString <- astToString uEq
      logInfoN $ "Asserting Shift equation (upper bound): " ++ eqUString
      return [lEq, uEq, soundness]
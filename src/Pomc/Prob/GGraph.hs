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
import Pomc.Prob.SupportGraph(GraphNode(..), Edge(..), SupportGraph)
import Pomc.Prob.ProbEncoding(ProbEncodedSet)
import qualified Pomc.Prob.ProbEncoding as PE
import qualified Pomc.Encoding as E
import Pomc.Prob.FixPoint(VarKey)
import Pomc.Z3T

import Data.Ratio ((%),)

import  Data.Strict.IntMap(IntMap)
import Data.Map(Map)
import qualified Data.Strict.IntMap as StrictIntMap
import qualified Data.Strict.Map as StrictMap
import qualified Data.Map as Map

import Data.Set(Set)
import qualified Data.Set as Set

import Data.IntSet(IntSet)
import qualified Data.IntSet as IntSet



import qualified Data.Vector.Mutable as MV
import Data.Vector(Vector, (!))
import qualified Data.Vector as V

import Data.Bifunctor(first)

import Control.Monad.IO.Class (MonadIO(liftIO))
import Control.Monad (when, unless, forM_, foldM, forM)
import Control.Monad.ST (ST, RealWorld)

import Data.STRef (STRef, newSTRef, readSTRef, modifySTRef')
import Data.Maybe (fromJust, isNothing, isJust, mapMaybe)

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
  , edges      :: IntMap ProbEncodedSet
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

-- the G Graph computed by this function
type GGraph s = CM.CustoMap s GNode

-- the global variables in the algorithm for constructing graph G
data GGlobals s pstate = GGlobals
  { idSeq      :: STRef s Int
  , ggraphMap   :: HashTable s (Int, State) Int
  , gGraph      :: STRef s (GGraph s)
  , grGlobals   :: GR.GRobals s (AugState pstate)
  }

-- requires: the initial semiconfiguration has id 0
-- requires: idSeq is at 0
-- pstate: a parametric type for states of the input popa
buildGGraph :: (Ord pstate, Hashable pstate, Show pstate)
                => GGlobals s pstate
                -> DeltaWrapper pstate
                -> [State] -- initial states of the phiOpa 
                -> SupportGraph pstate
                -> (Int -> Bool) -- is a semiconf pending?
                -> StrictMap.Map pstate Int
                -> ST s (GGraph s, Int)
buildGGraph gglobals delta phiInitials suppGraph isPending sIdMap = do
  let iniGn = suppGraph ! 0
      iniLabel = getLabel . fst . semiconf $ iniGn
  currentIdSeq <- readSTRef $ idSeq gglobals
  when (currentIdSeq /= 0) $ error "memory found containing some trash values when building graph G"
  filtered <- mapM (\s -> do
    -- create a new GNode 
    newId <- freshPosId (idSeq gglobals)
    BH.insert (ggraphMap gglobals) (gnId iniGn, s) newId
    CM.insert (gGraph gglobals) newId
      $ GNode {gId= newId, graphNode = gnId iniGn, phiNode = s, edges = StrictIntMap.empty, iValue = 0, descSccs = IntSet.empty}
    return s) (filter (\s -> iniLabel == E.extractInput (bitenc delta) (current s)) phiInitials)
  initialNodesBound <- readSTRef . idSeq $ gglobals
  forM_ filtered $ \s -> build gglobals delta suppGraph isPending sIdMap (iniGn, s)
  idx <- readSTRef . idSeq $ gglobals
  g <- CM.take idx <$> readSTRef (gGraph gglobals)
  return (g, initialNodesBound)

build :: (Ord pstate, Hashable pstate, Show pstate)
  => GGlobals s pstate -- global variables of the algorithm
  -> DeltaWrapper pstate
  -> SupportGraph pstate
  -> (Int -> Bool) -- is a semiconf pending?
  -> StrictMap.Map pstate Int
  -> (GraphNode pstate, State) -- current GNode
  -> ST s ()
build gglobals delta suppGraph isPending sIdMap (gn, p) =
  let (q,g) = semiconf gn
      precRel = (prec delta) (fst . fromJust $ g) (getLabel q)
      cases
        -- a sanity check
        | getLabel q /= E.extractInput (bitenc delta) (current p) = 
            error "inconsistent GNode when building the G Graph"

        -- this case includes the initial push
        | (isNothing g) || precRel == Just Yield =
            buildPush gglobals delta suppGraph isPending sIdMap (gn,p)

        | precRel == Just Equal =
            buildShift gglobals delta suppGraph isPending sIdMap (gn, p)

        | precRel == Just Take = 
            error $ "a pop transition cannot be reached in the augmented graph of pending semiconfs, as it terminates almost surely" ++ show gn
        
        | otherwise = return ()
  in cases


buildPush :: (Ord pstate, Hashable pstate, Show pstate)
  => GGlobals s pstate -- global variables of the algorithm
  -> DeltaWrapper pstate
  -> SupportGraph pstate
  -> (Int -> Bool) -- is a semiconf pending?
  -> StrictMap.Map pstate Int
  -> (GraphNode pstate, State) -- current gnode
  -> ST s ()
buildPush gglobals delta suppGraph isPending sIdMap (gn, p) =
  let getGns = map (suppGraph !) . Set.toList . Set.filter isPending . Set.map to
      fPushGns = getGns $ internalEdges gn
      fSuppGns = getGns $ supportEdges gn
      fPushPhiStates = (phiDeltaPush delta) p
      leftContext = AugState (fst . semiconf $ gn) p
      precRel = (prec delta)
      currentInput q = E.extractInput (bitenc delta) (current q)
      fPushGnodes = 
        [(gn1, p1) |
            gn1 <- fPushGns, p1 <- fPushPhiStates
          , (getLabel . fst . semiconf $ gn1) == currentInput p1
        ]
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
    fromId <- fromJust <$> BH.lookup (ggraphMap gglobals) (gnId gn, p)
    -- handling the push edges
    forM_ fPushGnodes $ \(gn1, p1) ->
      buildEdge gglobals delta suppGraph isPending sIdMap fromId (PE.empty . proBitenc $ delta) (gn1, p1)
    -- handling the support edges
    fSuppAugStates <- if not . null $ fSuppGns
                        then GR.reachableStates (grGlobals gglobals) cDelta leftContext
                        else return []
    unless (all (consistentFilter. fst) fSuppAugStates) $ error "a support Augmented State is inconsistent"
    let fSuppGnodes =
          [(gn1, p1, suppSatSet) |
              gn1 <- fSuppGns
            , (AugState (StateId _ q _) p1, suppSatSet) <- fSuppAugStates
            , (getState . fst . semiconf $ gn1) == q
          ]
    forM_ fSuppGnodes $ \(gn1, p1, suppSatSet) ->
      buildEdge gglobals delta suppGraph isPending sIdMap fromId suppSatSet (gn1, p1)

buildShift :: (Ord pstate, Hashable pstate, Show pstate)
  => GGlobals s pstate -- global variables of the algorithm
  -> DeltaWrapper pstate
  -> SupportGraph pstate
  -> (Int -> Bool) -- is a semiconf pending?
  -> StrictMap.Map pstate Int
  -> (GraphNode pstate, State) -- current GNopde
  -> ST s ()
buildShift gglobals delta suppGraph isPending sIdMap (gn, p) =
  let fGns = map (suppGraph !) . Set.toList . Set.filter isPending . Set.map to $ internalEdges gn
      fPhiStates = (phiDeltaShift delta) p
      fGnodes =
        [(gn1, p1) |
          gn1 <- fGns, p1 <- fPhiStates,
          (getLabel . fst . semiconf $ gn1) == E.extractInput (bitenc delta) (current p1)
        ]
  in do
    fromId <- fromJust <$> BH.lookup (ggraphMap gglobals) (gnId gn, p)
    forM_ fGnodes $ \(gn1, p1) ->
      buildEdge gglobals delta suppGraph isPending sIdMap fromId (PE.empty . proBitenc $ delta) (gn1, p1)

-- decomposing an edge to a new node
buildEdge :: (Ord pstate, Hashable pstate, Show pstate)
  => GGlobals s pstate -- global variables of the algorithm
  -> DeltaWrapper pstate
  -> SupportGraph pstate
  -> (Int -> Bool) -- is a semiconf pending?
  -> StrictMap.Map pstate Int
  -> Int-- id of current node
  -> ProbEncodedSet -- for formulae satisfied in a support
  -> (GraphNode pstate, State) -- to node
  -> ST s ()
buildEdge gglobals delta suppGraph isPending sIdMap fromId suppSatSet (gn1, p1) =
  let
    insertEdge to_  g@GNode{edges = edges_} = g{edges = StrictIntMap.insertWith PE.union to_ suppSatSet edges_}
  in do
    maybeId <- BH.lookup (ggraphMap gglobals) (gnId gn1, p1)
    actualId <- maybe (freshPosId $ idSeq gglobals) return maybeId
    when (isNothing maybeId) $ do
        BH.insert (ggraphMap gglobals) (gnId gn1, p1) actualId
        CM.insert (gGraph gglobals) actualId
          $ GNode {gId= actualId, graphNode = gnId gn1, phiNode = p1, edges = StrictIntMap.empty, iValue = 0, descSccs = IntSet.empty}
    CM.modify (gGraph gglobals) (insertEdge actualId) fromId
    when (isNothing maybeId) $ build gglobals delta suppGraph isPending sIdMap (gn1, p1)

-------- finding the bottom SCCs of subgraph H -------------
type GraphNodesSCC = IntSet

-- global variables for building and studying subgraph H
data HGlobals s pstate = HGlobals
  { graph :: GGraph s
  , sStack     :: GStack s HEdge
  , bStack     :: GStack s Int
  , cGabow     :: STRef s Int
  --  in qualitative model checking, we store only those reachable from a not phi initial state
  , bottomHSCCs  :: STRef s (IntMap GraphNodesSCC)
  }

data HEdge = Internal {toG :: Int} |
  Support {toG :: Int, satSet :: ProbEncodedSet}
  deriving Show

instance Eq HEdge where
  p == q = (toG p) == (toG q)

instance Ord HEdge where
  compare p q = compare (toG p) (toG q)

-- requires: the initial semiconfiguration has id 0
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
  -- global data structures for constructing graph G
  gGlobals <- liftSTtoIO $ do
    let numPendingSemiconfs = foldl (flip ((+) . fromEnum)) 0 pendVector
    newIdSequence <- newSTRef (0 :: Int)
    emptyGGraphMap <- BH.newSized numPendingSemiconfs
    emptyGGraph <- CM.emptySized numPendingSemiconfs
    emptyGRGlobals <- GR.newGRobals
    return GGlobals { idSeq = newIdSequence
                    , ggraphMap = emptyGGraphMap
                    , gGraph = emptyGGraph
                    , grGlobals = emptyGRGlobals
                    }

  logInfoN "Building graph G..."
  (gGraph_, iniCount) <- liftSTtoIO $ buildGGraph gGlobals delta phiInitials suppGraph (pendVector V.!) sIdMap
  logInfoN $ "Graph G has " ++ show (MV.length gGraph_) ++ " nodes."
  liftSTtoIO $ modifySTRef' stats (\s -> s {gGraphSize = (MV.length gGraph_) })

  logInfoN "Analyzing graph G..."
  -- globals data structures for qualitative model checking
  -- -1 is reserved for useless (i.e. single node) SCCs
  liftSTtoIO $ do
    sccCounter <- newSTRef (-2 :: Int)
    newSS         <- GS.new
    newBS         <- GS.new
    newFoundSCCs <- newSTRef StrictIntMap.empty
    let hGlobals = HGlobals { graph = gGraph_
                            , sStack = newSS
                            , bStack = newBS
                            , cGabow = sccCounter
                            , bottomHSCCs = newFoundSCCs
                            }
    (phiNodes, notPhiNodes) <- foldM
      (\(pn, npn) i -> do
        node <- MV.unsafeRead gGraph_ i
        if E.member (bitenc delta) phi . current . phiNode $ node
          then return (i:pn, npn)
          else return (pn, i:npn)
      ) ([],[]) [0.. (iniCount -1)]

    -- explore nodes where phi does not hold
    forM_ notPhiNodes $ \i -> do
      node <- MV.unsafeRead gGraph_ i
      when (iValue node == 0) $
        addtoPath hGlobals node (Internal (gId node)) >>= dfs suppGraph hGlobals delta (pendVector V.!) False >> return ()
    -- explore nodes where phi does hold
    forM_ phiNodes $ \i -> do
      node <- MV.unsafeRead gGraph_ i
      nullCandidates <- StrictIntMap.null <$> readSTRef (bottomHSCCs hGlobals)
      when (iValue node == 0 && not nullCandidates) $
        addtoPath hGlobals node (Internal (gId node)) >>= dfs suppGraph hGlobals delta (pendVector V.!) True >> return ()
    -- returning whether there is a bottom SCC in H reachable from a not Phi initial node
    StrictIntMap.null <$> readSTRef (bottomHSCCs hGlobals)

dfs :: SupportGraph pstate
  -> HGlobals s pstate
  -> DeltaWrapper pstate
  -> (Int -> Bool) -- is a semiconf pending?
  -> Bool
  -> GNode
  -> ST s IntSet
dfs suppGraph hGlobals delta isPending fromPhi g =
  let
    -- creating an edge to push on the stack
    encodeEdge ident sss
        | PE.null sss = Internal ident
        | otherwise = Support ident sss
    -- different cases of the Gabow SCC algorithm
    cases e nextNode
      | (iValue nextNode == 0) = addtoPath hGlobals nextNode e >>= dfs suppGraph hGlobals delta isPending fromPhi
      | (iValue nextNode < 0)  = return (descSccs nextNode)
      -- I need to push anyway because I want to keep track of cycles in createComponent
      | (iValue nextNode > 0)  = GS.push (sStack hGlobals) e >> merge hGlobals nextNode >> return IntSet.empty
      | otherwise = error "unreachable error"
  in do
    descendantSCCs <-  forM (StrictIntMap.toList $ edges g)
      $ \(ident, sss) ->  MV.unsafeRead (graph hGlobals) ident >>= cases (encodeEdge ident sss)
    if fromPhi
      then createComponentPhi hGlobals g (IntSet.unions descendantSCCs)
      else createComponent suppGraph hGlobals delta isPending g (IntSet.unions descendantSCCs)


createComponent :: SupportGraph pstate -> HGlobals s pstate -> DeltaWrapper pstate -> (Int -> Bool) -> GNode -> IntSet -> ST s IntSet
createComponent suppGraph hGlobals delta isPending g descendantSCCs = do
  topB <- GS.peek $ bStack hGlobals
  if (iValue g) == topB
    then do
      GS.pop_ (bStack hGlobals)
      sSize <- GS.size $ sStack hGlobals
      poppedEdges <- GS.multPop (sStack hGlobals) (sSize - (iValue g) + 1) -- the last one is to gn
      if (length poppedEdges == 1)
        then do
          MV.modify (graph hGlobals) (\g -> g{iValue = -1, descSccs = descendantSCCs}) (gId g)
          return descendantSCCs
        else do
          -- discard all descendants that share a semiconf with the current one
          let sccEdges = init poppedEdges
          sccSemiconfs <- IntSet.fromList <$> forM sccEdges (\e -> graphNode <$> MV.unsafeRead (graph hGlobals) (toG e))
          filteredDescendants <- deleteDescendants hGlobals sccSemiconfs descendantSCCs
          -- check if current SCC is a candidate bottom SCC of H
          let isBott = isBottom suppGraph sccSemiconfs isPending
          isAccept <- isAccepting hGlobals delta sccEdges
          if isBott && isAccept
            then do
              newSCCid <- freshNegId (cGabow hGlobals)
              modifySTRef' (bottomHSCCs hGlobals) $ StrictIntMap.insert newSCCid sccSemiconfs
              let descs = IntSet.insert newSCCid filteredDescendants
              forM_ sccEdges $ \e -> MV.modify (graph hGlobals) (\g -> g{iValue = newSCCid, descSccs = descs}) (toG e)
              return descs
            else do
              forM_ sccEdges $ \e -> MV.modify (graph hGlobals) (\g -> g{iValue = -1, descSccs = filteredDescendants}) (toG e)
              return filteredDescendants
    else return descendantSCCs

createComponentPhi :: HGlobals s pstate -> GNode -> IntSet -> ST s IntSet
createComponentPhi hGlobals g descendantSCCs = do
  topB <- GS.peek $ bStack hGlobals
  if (iValue g) == topB
    then do
      GS.pop_ (bStack hGlobals)
      sSize <- GS.size $ sStack hGlobals
      sccEdges <- GS.multPop (sStack hGlobals) (sSize - (iValue g) + 1) -- the last one is to gn
      if length sccEdges == 1
        then do
          MV.modify (graph hGlobals) (\g -> g{iValue = -1, descSccs = descendantSCCs}) (gId g)
          return descendantSCCs
        else do
          -- discard all descendants that share a semiconf with the current one
          sccSemiconfs <- IntSet.fromList <$> forM sccEdges (\e -> graphNode <$> MV.unsafeRead (graph hGlobals) (toG e))
          filteredDescendants <- deleteDescendants hGlobals sccSemiconfs descendantSCCs
          forM_ sccEdges $ \e -> MV.modify (graph hGlobals) (\g -> g{iValue = -1, descSccs = filteredDescendants}) (toG e)
          return filteredDescendants
    else return descendantSCCs

-- Gabow helpers
addtoPath :: HGlobals s pstate -> GNode -> HEdge -> ST s GNode
addtoPath hglobals node edge  = do
  GS.push (sStack hglobals) edge
  sSize <- GS.size $ sStack hglobals
  MV.unsafeModify (graph hglobals) (\g -> g{iValue = sSize}) (gId node)
  GS.push (bStack hglobals) sSize
  return node{iValue = sSize}

merge :: HGlobals s pstate -> GNode -> ST s ()
merge hGlobals g = do
  -- contract the B stack, that represents the boundaries between SCCs on the current path
  GS.popWhile_ (bStack hGlobals) (\x -> iValue g < x)
-- end Gabow helpers

-- helpers for the construction of subgraph H
--
deleteDescendants :: HGlobals s pstate -> GraphNodesSCC -> IntSet -> ST s IntSet
deleteDescendants hGlobals sccSemiconfs descendants = do
  modifySTRef' (bottomHSCCs hGlobals) $ 
    StrictIntMap.filterWithKey (\idx scc -> not (IntSet.member idx descendants) || IntSet.disjoint sccSemiconfs scc)
  -- returning filtered descendants
  (\m -> IntSet.filter (`StrictIntMap.member` m) descendants) <$> readSTRef (bottomHSCCs hGlobals)

-- first necessary condition for an SCC to be in H
isBottom :: SupportGraph pstate -> IntSet -> (Int -> Bool) -> Bool
isBottom suppGraph suppGraphSCC isPending =
  let gns = map (suppGraph !) (IntSet.toList suppGraphSCC)
      bottomCheck = all (\e -> IntSet.member (to e) suppGraphSCC) . Set.filter (isPending . to)
  in all (\gn -> (bottomCheck . internalEdges) gn && (bottomCheck . supportEdges) gn) gns

-- second necessary condition for an SCC to be in H
isAccepting :: HGlobals s pstate -> DeltaWrapper pstate -> [HEdge] -> ST s Bool
isAccepting hGlobals delta sccEdges = do
  gs <- mapM (MV.unsafeRead (graph hGlobals) . toG) sccEdges
  let maybeSupport (Internal _ ) = Nothing
      maybeSupport (Support _ sss) = Just sss
      acceptanceBitVector = PE.unions $ map (PE.encodeSatState (proBitenc delta) . phiNode) gs ++ mapMaybe maybeSupport sccEdges
  return $ PE.isSatisfying acceptanceBitVector
--
-- end helpers for the construction of subgraph H

-- quantitative model checking --
-- requires: the initial semiconfiguration has id 0
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
  -- global data structures for constructing graph G
  gGlobals <- liftSTtoIO $ do
    newIdSequence <- newSTRef (0 :: Int)
    let numPendingSemiconfs = foldl (flip ((+) . fromEnum)) 0 pendVector
    emptyGGraphMap <- BH.newSized numPendingSemiconfs
    emptyGGraph <- CM.emptySized numPendingSemiconfs
    emptyGRGlobals <- GR.newGRobals
    return GGlobals { idSeq = newIdSequence
                    , ggraphMap = emptyGGraphMap
                    , gGraph = emptyGGraph
                    , grGlobals = emptyGRGlobals
                    }
  logInfoN "Building graph G..."
  (computedGraph, iniCount) <- liftSTtoIO $ buildGGraph gGlobals delta phiInitials suppGraph (pendVector V.!) sIdMap
  logInfoN $ "Graph G has " ++ show (MV.length computedGraph) ++ " nodes."

  liftSTtoIO $ modifySTRef' stats (\s -> s {gGraphSize = MV.length computedGraph})
  logInfoN "Analyzing graph G..."

  -- globals data structures for qualitative model checking
  -- -1 is reserved for useless (i.e. single node) SCCs
  hGlobals <- liftSTtoIO $ do
    sccCounter   <- newSTRef (-2 :: Int)
    newSS        <- GS.new
    newBS        <- GS.new
    newFoundSCCs <- newSTRef StrictIntMap.empty
    return HGlobals { graph = computedGraph
                    , sStack = newSS
                    , bStack = newBS
                    , cGabow = sccCounter
                    , bottomHSCCs = newFoundSCCs
                    }

  -- computing all the bottom SCCs of graph H
  phiInitialGNodesIdxs <- foldM (\acc idx -> do
    node <- liftSTtoIO $ MV.unsafeRead computedGraph idx
    when (iValue node == 0) $ liftSTtoIO $ do
      addedNode <- addtoPath hGlobals node (Internal (gId node))
      _ <- dfs suppGraph hGlobals delta (pendVector V.!) False addedNode
      return ()
    if E.member (bitenc delta) phi . current . phiNode $ node
      then return (idx:acc)
      else return acc
    ) [] [0.. (iniCount -1)]

  hSCCs <- liftSTtoIO $ StrictIntMap.keysSet <$> readSTRef (bottomHSCCs hGlobals)
  freezedGGraph <- liftSTtoIO $ V.freeze computedGraph

  logInfoN "Computed qualitative model checking..."
  tGG <- stopTimer startGGTime hSCCs
  liftSTtoIO $ modifySTRef' stats (\s -> s {gGraphTime = tGG })

  -- bottomString <- show <$> readSTRef (bottomHSCCs hGlobals)
  -- gString <- CM.showMap computedGraph
  -- logDebugN gString
  -- logDebugN bottomString

  -- computing the probability of satisfying the temporal formula
  let isInH g = not . IntSet.null . IntSet.intersection hSCCs $ descSccs g
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

    logInfoN "Generated z3 vars for encoding (2)"

    -- preparing the global variables for the computation of the fractions f
    freezedSuppEnds <- liftIO $ GR.freezeSuppEnds (grGlobals gGlobals)

    lenHashtables <- liftSTtoIO $ GR.nrSemiconfs (grGlobals gGlobals)
    globals <- GR.newWeightedGRobals lenHashtables stats

    logInfoN "Encoding conditions (2b) and (2c)"
    -- encodings (2b) and (2c)
    encs1 <- concat <$> mapM
      (\gNode -> encode
          globals (GR.sIdGen (grGlobals gGlobals)) freezedSuppEnds delta
          (newlMap, newuMap) suppGraph freezedGGraph (prec delta) isInH gNode
          pendProbsLowerBounds pendProbsUpperBounds sIdMap (useNewton solv)
      ) (V.filter isInH freezedGGraph)

    logInfoN "Encoding conditions (2a)"
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

encodeTransition :: MonadZ3 z3 => [Prob] -> [Prob] -> AST -> z3 AST
encodeTransition probsMul probsDiv toVar = do
  astProbsMul <- mapM mkRational probsMul
  astProbsDiv <- mkAdd =<< mapM mkRational probsDiv
  numerator <- mkMul $ astProbsMul ++ [toVar]
  mkDiv numerator astProbsDiv

encode :: (MonadZ3 z3, MonadFail z3, MonadLogger z3, Ord pstate, Hashable pstate, Show pstate)
      => GR.WeightedGRobals (AugState pstate)
      -> SIdGen RealWorld (AugState pstate)
      -> Vector (Set (SU.StateId (AugState pstate)))
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
encode wGrobals sIdGen supports delta (lTypVarMap, uTypVarMap) suppGraph gGraph precFun isInH gNode pendProbsLB pendProbsUB sIdMap useNewton =
  let gn = suppGraph ! graphNode gNode
      (q,g) = semiconf gn
      qLabel = getLabel q
      precRel = precFun (fst . fromJust $ g) qLabel -- safe due to laziness
      cases
        -- this case includes the initial push
        | isNothing g || precRel == Just Yield =
            encodePush wGrobals sIdGen supports delta (lTypVarMap, uTypVarMap) suppGraph
              gGraph isInH gNode gn pendProbsLB pendProbsUB sIdMap useNewton

        | precRel == Just Equal =
            encodeShift (lTypVarMap, uTypVarMap) gGraph isInH gNode gn pendProbsLB pendProbsUB

        | otherwise = fail "unexpected prec rel"
   in cases

-- encoding helpers --
encodePush :: (MonadZ3 z3, MonadFail z3, MonadLogger z3, Ord pstate, Hashable pstate, Show pstate)
  => GR.WeightedGRobals (AugState pstate)
  -> SIdGen RealWorld (AugState pstate)
  -> Vector (Set(SU.StateId (AugState pstate)))
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
encodePush wGrobals sIdGen supports delta (lTypVarMap, uTypVarMap) suppGraph gGraph isInH g gn pendProbsLB pendProbsUB sIdMap useNewton =
  let fNodes = IntSet.toList . IntSet.filter (isInH . (gGraph V.!)) . StrictIntMap.keysSet $ edges g
      pushEnc toIdx = do
        tolVar <- liftIO $ fromJust <$> HT.lookup lTypVarMap toIdx
        touVar <- liftIO $ fromJust <$> HT.lookup uTypVarMap toIdx
        let toG = gGraph ! toIdx
            -- push edges in the support Graph
            maybePPush = Set.lookupLE (Edge (graphNode toG) 0) $ internalEdges gn
            probPush = prob $ fromJust maybePPush
            isPushEdge = isJust maybePPush && to (fromJust maybePPush) == graphNode toG &&
              elem (phiNode toG) (phiDeltaPush delta $ phiNode g)
            encodePushTrans = do
              lT <- encodeTransition [probPush, pendProbsLB ! (graphNode toG)] [pendProbsUB V.! (graphNode g)] tolVar
              uT <- encodeTransition [probPush, pendProbsUB ! (graphNode toG)] [pendProbsLB V.! (graphNode g)] touVar
              return [(lT, uT)]
            -- supports edges in the Support Graph
            maybePSupport = Set.lookupLE (Edge (graphNode toG) 0) $ supportEdges gn
            isSuppEdge = isJust maybePSupport && to (fromJust maybePSupport) == (graphNode toG)
            supportGn = suppGraph V.! (graphNode toG)
            -- augmented states in the cross product
            leftContext = AugState (fst . semiconf $ gn) (phiNode g)
            rightContext = AugState (fst . semiconf $ supportGn) (phiNode toG)
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
                ++ show (gId g) ++ " to H node " ++ show (gId toG)
              (lW, uW) <- GR.weightQuerySCC wGrobals sIdGen cDelta supports leftContext rightContext useNewton
              lT <- encodeTransition [lW, pendProbsLB V.! (graphNode toG)] [pendProbsUB V.! (graphNode g)] tolVar
              uT <- encodeTransition [uW, pendProbsUB V.! (graphNode toG)] [pendProbsLB V.! (graphNode g)] touVar
              return [(lT, uT)]
            cases
              | isPushEdge && isSuppEdge = do
                  pushEncs <- encodePushTrans
                  suppEncs <- encodeSupportTrans
                  return (pushEncs ++ suppEncs)
              | isPushEdge = encodePushTrans
              | isSuppEdge = encodeSupportTrans
              | otherwise = error "there must be at least one edge in the support graph associated with this edge in graph H"
        cases
        -- end pushEnc
  in do
    -- a little sanity check
    unless (graphNode g == gnId gn) $ error "Encoding Push corresponding to non consistent pair GNode - graphNode"
    lvar <- liftIO $ fromJust <$> HT.lookup lTypVarMap (gId g)
    uvar <- liftIO $ fromJust <$> HT.lookup uTypVarMap (gId g)
    if fNodes == [gId g]
      then do
        lEqOne <- mkEq lvar =<< mkRational (1 :: Prob)
        uEqOne <- mkEq uvar =<< mkRational (1 :: Prob)
        return [lEqOne, uEqOne]
      else do
        transitions <- concat <$> mapM pushEnc fNodes
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
            -> GraphNode pstate
            -> Vector Prob
            -> Vector Prob
            -> z3 [AST]
encodeShift (lTypVarMap, uTypVarMap) gGraph isInH g gn pendProbsLB pendProbsUB =
  let fNodes = IntSet.toList . IntSet.filter (isInH . (gGraph V.!)) . StrictIntMap.keysSet $ edges g
      shiftEnc toIdx = do
        tolVar <- liftIO $ fromJust <$> HT.lookup lTypVarMap toIdx
        touVar <- liftIO $ fromJust <$> HT.lookup uTypVarMap toIdx
        -- a small trick to be refactored later
        let toG = gGraph V.! toIdx
            p = prob . fromJust . Set.lookupLE (Edge (graphNode toG) 0) $ internalEdges gn
        lT <- encodeTransition [p, pendProbsLB V.! (graphNode toG)] [pendProbsUB V.! (graphNode g)] tolVar
        uT <- encodeTransition [p, pendProbsUB V.! (graphNode toG)] [pendProbsLB V.! (graphNode g)] touVar
        return (lT, uT)

  in do
  -- a little sanity check
  unless (graphNode g == gnId gn) $ error "Encoding Shift encountered a non consistent pair GNode - graphNode"
  lvar <- liftIO $ fromJust <$> HT.lookup lTypVarMap (gId g)
  uvar <- liftIO $ fromJust <$> HT.lookup uTypVarMap (gId g)
  -- it's greater than zero for sure!
  if fNodes == [gId g]
    then do
      lEqOne <- mkEq lvar =<< mkRational (1 :: Prob)
      uEqOne <- mkEq uvar =<< mkRational (1 :: Prob)
      return [lEqOne, uEqOne]
    else do
      transitions <- mapM shiftEnc fNodes
      lEq <- mkGe lvar =<< mkAdd (map fst transitions)
      uEq <- mkLe uvar =<< mkAdd (map snd transitions)
      soundness <- mkLe lvar uvar
      -- debugging
      eqLString <- astToString lEq
      logInfoN $ "Asserting Shift equation (lower bound): " ++ eqLString
      eqUString <- astToString uEq
      logInfoN $ "Asserting Shift equation (upper bound): " ++ eqUString
      return [lEq, uEq, soundness]
{-# LANGUAGE DeriveGeneric #-}
{- |
   Module      : Pomc.Prob.GGraph
   Copyright   : 2023 Francesco Pontiggia
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
import Pomc.LogUtils (MonadLogger, logDebugN, logInfoN)
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
import qualified Pomc.IOStack as IOGS
import qualified Pomc.Encoding as E
import Pomc.Prob.FixPoint(VarKey)

-- TODO: check whether replacing with Data.Strict.Map
import  Data.Strict.IntMap(IntMap)
import qualified Data.Strict.IntMap as Map

import Data.Map(Map)
import qualified Data.Map as GeneralMap

import Data.Set(Set)
import qualified Data.Set as Set

import Data.IntSet(IntSet)
import qualified Data.IntSet as IntSet

import qualified Data.Strict.Map as StrictMap

import qualified Data.Vector.Mutable as MV
import Data.Vector(Vector, (!))
import qualified Data.Vector as V

import Control.Monad.IO.Class (MonadIO(liftIO))
import Control.Monad (when, unless, forM_, foldM, forM)
import Control.Monad.ST (ST, RealWorld)

import Data.STRef (STRef, newSTRef, readSTRef, modifySTRef')
import Data.IORef (newIORef)
import Data.Maybe (fromJust, isNothing, isJust, mapMaybe)

import GHC.Generics (Generic)
import Data.Hashable
import qualified Data.HashTable.IO as HT
import qualified Data.HashTable.ST.Basic as BH

import Z3.Monad
import Pomc.Z3T
import qualified Pomc.IOMapMap as MM

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
  hashWithSalt salt (AugState sId phiState) = hashWithSalt salt $ (getId sId, phiState)

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
                        $ GNode {gId= newId, graphNode = gnId iniGn, phiNode = s, edges = Map.empty, iValue = 0, descSccs = IntSet.empty}
                      return s
                   ) (filter (\s -> iniLabel == E.extractInput (bitenc delta) (current s)) phiInitials)
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
        | getLabel q /= E.extractInput (bitenc delta) (current p) = error "inconsistent GNode when building the G Graph"

        -- this case includes the initial push
        | (isNothing g) || precRel == Just Yield =
          buildPush gglobals delta suppGraph isPending sIdMap (gn,p)

        | precRel == Just Equal =
          buildShift gglobals delta suppGraph isPending sIdMap (gn, p)

        | precRel == Just Take = error $ "a pop transition cannot be reached in the augmented graph of pending semiconfs, as it terminates almost surely" ++ show gn
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
  let fPushGns = map (suppGraph !) . Set.toList . Set.filter isPending . Set.map to $ internalEdges gn
      fSuppGns = map (suppGraph !) . Set.toList . Set.filter isPending . Set.map to $ supportEdges gn
      fPushPhiStates = (phiDeltaPush delta) p
      fPushGnodes = [(gn1, p1) | gn1 <- fPushGns, p1 <- fPushPhiStates, (getLabel . fst . semiconf $ gn1) == E.extractInput (bitenc delta) (current p1)]
      leftContext = AugState (fst . semiconf $ gn) p
      precRel stackSymbol qProps = (prec delta) stackSymbol qProps
      cDeltaPush (AugState (StateId _ q0 lab0) p0)  =  [(AugState (StateId id1 q1 lab1) p1, prob_) |
                                                          (q1, lab1, prob_) <- (deltaPush delta) q0
                                                        , p1 <- (phiDeltaPush delta) p0
                                                        , (precRel lab0 lab1 == Just Take)
                                                          || lab1 == E.extractInput (bitenc delta) (current p1)
                                                        , let id1 = sIdMap StrictMap.! q1]
      cDeltaShift (AugState (StateId _ q0 lab0) p0) =  [ (AugState (StateId id1 q1 lab1) p1, prob_) |
                                                         (q1, lab1, prob_) <- (deltaShift delta) q0
                                                        , p1 <- (phiDeltaShift delta) p0
                                                        , (precRel lab0 lab1 == Just Take) || lab1 == E.extractInput (bitenc delta) (current p1)
                                                        , let id1 = sIdMap StrictMap.! q1
                                                        ]
      cDeltaPop (AugState (StateId _ q0 _) p0) (AugState (StateId _ q1 _) p1)  = [(AugState (StateId id2 q2 lab2) p2, prob_) |
                                                                                    (q2, lab2, prob_) <- (deltaPop delta) q0 q1
                                                                                  , let id2 = sIdMap StrictMap.! q2
                                                                                  , p2 <- (phiDeltaPop delta) p0 p1]

      consistentFilter (AugState sId0 p0) = (getLabel sId0) == E.extractInput (bitenc delta) (current p0)
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
    -- handling the push edges
    forM_ fPushGnodes $ \(gn1, p1) -> buildEdge gglobals delta suppGraph isPending sIdMap (gn, p) (PE.empty . proBitenc $ delta) (gn1, p1)
    -- handling the support edges
    fSuppAugStates <- if not . null $ fSuppGns
                        then  GR.reachableStates (grGlobals gglobals) cDelta leftContext
                        else return []
    unless (all (consistentFilter. fst) fSuppAugStates) $ error "a support Augmented State is inconsistent"
    let fSuppGnodes = [(gn1, p1, suppSatSet) |
                        gn1 <- fSuppGns
                      , (AugState (StateId _ q _) p1, suppSatSet) <- fSuppAugStates
                      , (getState . fst . semiconf $ gn1) == q
                      ]
    forM_ fSuppGnodes $ \(gn1, p1, suppSatSet) -> buildEdge gglobals delta suppGraph isPending sIdMap (gn, p) suppSatSet (gn1, p1)

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
      fGnodes = [(gn1, p1) | gn1 <- fGns, p1 <- fPhiStates, (getLabel . fst . semiconf $ gn1) == E.extractInput (bitenc delta) (current p1)]
  in forM_ fGnodes $ \(gn1, p1) -> buildEdge gglobals delta suppGraph isPending sIdMap (gn, p) (PE.empty . proBitenc $ delta) (gn1, p1)

-- decomposing an edge to a new node
buildEdge :: (Ord pstate, Hashable pstate, Show pstate)
                 => GGlobals s pstate -- global variables of the algorithm
                 -> DeltaWrapper pstate
                 -> SupportGraph pstate
                 -> (Int -> Bool) -- is a semiconf pending?
                 -> StrictMap.Map pstate Int
                 -> (GraphNode pstate, State) -- current node
                 -> ProbEncodedSet -- for formulae satisfied in a support
                 -> (GraphNode pstate, State) -- to node
                 -> ST s ()
buildEdge gglobals delta suppGraph isPending sIdMap (gn, p) suppSatSet (gn1, p1) =
  let
    insertEdge to_  g@GNode{edges = edges_} = g{edges = Map.insertWith PE.union to_ suppSatSet edges_}
    lookupInsert to_ = BH.lookup (ggraphMap gglobals) (gnId gn, p) >>= CM.modify (gGraph gglobals) (insertEdge to_) . fromJust
  in do
    maybeId <- BH.lookup (ggraphMap gglobals) (gnId gn1, p1)
    actualId <- maybe (freshPosId $ idSeq gglobals) return maybeId
    when (isNothing maybeId) $ do
        BH.insert (ggraphMap gglobals) (gnId gn1, p1) actualId
        CM.insert (gGraph gglobals) actualId $ GNode {gId= actualId, graphNode = gnId gn1, phiNode = p1, edges = Map.empty, iValue = 0, descSccs = IntSet.empty}
    lookupInsert actualId
    when (isNothing maybeId) $ build gglobals delta suppGraph isPending sIdMap (gn1, p1)

-------- finding the bottom SCCs of subgraph H -------------
type GraphNodesSCC = IntSet

data HGlobals s pstate = HGlobals
  { graph :: GGraph s
  , sStack     :: GStack s HEdge
  , bStack     :: GStack s Int
  , cGabow     :: STRef s Int
  , bottomHSCCs  :: STRef s (IntMap GraphNodesSCC) --  in qualitative model checking, we store only those reachable from a not phi initial state
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
                      -> m Bool
qualitativeModelCheck delta phi phiInitials suppGraph sIdMap pendVector = do
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
  logInfoN "Analyzing graph G..."
  -- globals data structures for qualitative model checking
  -- -1 is reserved for useless (i.e. single node) SCCs
  liftSTtoIO $ do
    sccCounter <- newSTRef (-2 :: Int)
    newSS         <- GS.new
    newBS         <- GS.new
    newFoundSCCs <- newSTRef Map.empty
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
      nullCandidates <- Map.null <$> readSTRef (bottomHSCCs hGlobals)
      when (iValue node == 0 && not nullCandidates) $
        addtoPath hGlobals node (Internal (gId node)) >>= dfs suppGraph hGlobals delta (pendVector V.!) True >> return ()
    -- returning whether there is a bottom SCC in H reachable from a not Phi initial node
    Map.null <$> readSTRef (bottomHSCCs hGlobals)

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
    descendantSCCs <-  forM (Map.toList $ edges g)
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
              modifySTRef' (bottomHSCCs hGlobals) $ Map.insert newSCCid sccSemiconfs
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
  modifySTRef' (bottomHSCCs hGlobals) $ Map.filterWithKey (\idx scc -> not (IntSet.member idx descendants) || IntSet.disjoint sccSemiconfs scc)
  -- returning filtered descendants
  (\m -> IntSet.filter (`Map.member` m) descendants) <$> readSTRef (bottomHSCCs hGlobals)

-- first necessary condition for an SCC to be in H
isBottom :: SupportGraph pstate -> IntSet -> (Int -> Bool) -> Bool
isBottom suppGraph suppGraphSCC isPending =
  let gns = map (suppGraph !) (IntSet.toList suppGraphSCC)
      checkInternals = all (\e -> IntSet.member (to e) suppGraphSCC) . Set.filter (isPending . to) . internalEdges
      checkSupports  = all (\e -> IntSet.member (to e) suppGraphSCC) . Set.filter (isPending . to) . supportEdges
  in all (\gn -> checkInternals gn && checkSupports gn) gns

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
                       -> m (Prob, Prob)
quantitativeModelCheck delta phi phiInitials suppGraph pendVector lowerBounds upperBounds sIdMap oldStats = do
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
  (computedGraph, iniCount) <- liftSTtoIO $ buildGGraph gGlobals delta phiInitials suppGraph (pendVector V.!) sIdMap
  -- globals data structures for qualitative model checking
  -- -1 is reserved for useless (i.e. single node) SCCs
  hGlobals <- liftSTtoIO $ do
    sccCounter   <- newSTRef (-2 :: Int)
    newSS        <- GS.new
    newBS        <- GS.new
    newFoundSCCs <- newSTRef Map.empty
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

  hSCCs <- liftSTtoIO $ Map.keysSet <$> readSTRef (bottomHSCCs hGlobals)
  freezedGGraph <- liftSTtoIO $ V.freeze computedGraph

  logInfoN "Computed qualitative model checking..."
  tGG <- stopTimer startGGTime hSCCs
  liftSTtoIO $ modifySTRef' oldStats (\s -> s {gGraphTime = tGG })

  -- bottomString <- show <$> readSTRef (bottomHSCCs hGlobals)
  -- gString <- CM.showMap computedGraph
  -- logDebugN gString
  -- logDebugN bottomString

  -- computing the probability of satisfying the temporal formula
  let isInH g = not . IntSet.null . IntSet.intersection hSCCs $ descSccs g
      lowerBoundsMap = Map.fromListWith (+) . map (\(k, p) -> (fst k, p)) . GeneralMap.toList $ lowerBounds
      upperBoundsMap = Map.fromListWith (+) . map (\(k, p) -> (fst k, p)) . GeneralMap.toList $ upperBounds

      pendProbsUpperBounds = V.generate (V.length suppGraph) (\idx -> 1 - Map.findWithDefault 0 idx lowerBoundsMap)
      pendProbsLowerBounds = V.generate (V.length suppGraph) (\idx -> 1 - Map.findWithDefault 0 idx upperBoundsMap)

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

    globals <- liftIO $ do
      newIdSeq <- newIORef 0
      newGraphMap <- HT.new
      newSStack <- IOGS.new
      newBStack <- IOGS.new
      newIVector <- HT.new
      newScntxs <- HT.new
      newLowerEqMap <- MM.empty
      newUpperEqMap <- MM.empty
      newLowerLiveVars <- newIORef Set.empty
      newUpperLiveVars <- newIORef Set.empty
      newEps <- newIORef defaultTolerance
      return GR.WeightedGRobals { GR.idSeq = newIdSeq
                                , GR.graphMap = newGraphMap
                                , GR.sStack = newSStack
                                , GR.bStack = newBStack
                                , GR.iVector = newIVector
                                , GR.successorsCntxs = newScntxs
                                , GR.lowerEqMap = (newLowerEqMap, newLowerLiveVars)
                                , GR.upperEqMap = (newUpperEqMap, newUpperLiveVars)
                                , GR.actualEps = newEps
                                , GR.stats = oldStats
                                }

    logInfoN "Encoding conditions (2b) and (2c)"
    -- encodings (2b) and (2c)
    encs1 <- concat <$> mapM
      (\gNode -> encode
        globals (GR.sIdGen (grGlobals gGlobals)) freezedSuppEnds delta (newlMap, newuMap) suppGraph freezedGGraph (prec delta) isInH gNode pendProbsLowerBounds pendProbsUpperBounds sIdMap
      ) (V.filter isInH freezedGGraph)

    logInfoN "Encoding conditions (2a)"
    -- encoding (2a) for lower bounds
    groupedlMaptoList <- liftIO (HT.toList newlGroupedMap)
    encs2 <- foldM (\acc (_, vList) -> do
        vSum <- mkAdd vList
        lConstr1 <- mkLe vSum =<< mkRational (1 :: Prob)
        lConstr2 <- mkGe vSum =<< mkRational (1 - defaultRTolerance)
        return (lConstr1:lConstr2:acc)
      ) [] groupedlMaptoList

    -- encoding (2a) for upper bounds
    groupeduMaptoList <- liftIO (HT.toList newuGroupedMap)
    encs3 <- foldM (\acc (_, vList) -> do
      vSum <- mkAdd vList
      uConstr1 <- mkGe vSum =<< mkRational (1 :: Prob)
      uConstr2 <- mkLe vSum =<< mkRational (1 + defaultRTolerance)
      return (uConstr1:uConstr2:acc)
      ) [] groupeduMaptoList

    -- computing a lower bound on the probability to satisfy the given property
    let phiInitialGNodesIdxsinH = filter (\idx -> isInH (freezedGGraph V.! idx)) phiInitialGNodesIdxs
    philVars <- liftIO $ mapM  (fmap fromJust . HT.lookup newlMap) phiInitialGNodesIdxsinH
    phiuVars <- liftIO $ mapM  (fmap fromJust . HT.lookup newuMap) phiInitialGNodesIdxsinH

    sumlVar <- mkAdd philVars
    sumuVar <- mkAdd phiuVars

    startSol <- startTimer
    mapM_ assert encs1 >> mapM_ assert encs2 >> mapM_ assert encs3
    logInfoN "Calling Z3 to solve quantitative model checking..."
    logInfoN "In the new implementation it is too expensive to compute the number of stored equations"
    (lb, ub) <- fromJust . snd <$> withModel (\model -> do
      l <- extractLowerProb . fromJust =<< eval model sumlVar
      u <- extractUpperProb . fromJust =<< eval model sumuVar
      logInfoN $ "Computed lower bound on the quantitative probability: " ++ show l
      logInfoN $ "Computed upper bound on the quantitative probability: " ++ show u
      return (l, u))

    tSol <- stopTimer startSol ub
    liftSTtoIO $ modifySTRef' oldStats (\s -> s { quantSolTime = quantSolTime s + tSol})

    return (lb, ub)

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
      -> z3 [AST]
encode wGrobals sIdGen supports delta (lTypVarMap, uTypVarMap) suppGraph gGraph precFun isInH gNode pendProbsLB pendProbsUB sIdMap =
  let gn = suppGraph ! graphNode gNode
      (q,g) = semiconf gn
      qLabel = getLabel q
      precRel = precFun (fst . fromJust $ g) qLabel -- safe due to laziness
      cases
        -- this case includes the initial push
        | isNothing g || precRel == Just Yield =
            encodePush wGrobals sIdGen supports delta (lTypVarMap, uTypVarMap) suppGraph gGraph isInH gNode gn pendProbsLB pendProbsUB sIdMap

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
  -> z3 [AST]
encodePush wGrobals sIdGen supports delta (lTypVarMap, uTypVarMap) suppGraph gGraph isInH g gn pendProbsLB pendProbsUB sIdMap =
  let fNodes = IntSet.toList . IntSet.filter (\idx -> isInH (gGraph V.! idx)) . Map.keysSet $ edges g
      pushEnc toIdx = do
        tolVar <- liftIO $ fromJust <$> HT.lookup lTypVarMap toIdx
        touVar <- liftIO $ fromJust <$> HT.lookup uTypVarMap toIdx
        let toG = gGraph ! toIdx
            -- push edges in the support Graph
            maybePPush = Set.lookupLE (Edge (graphNode toG) 0) $ internalEdges gn
            probPush = prob $ fromJust maybePPush
            encodePushTrans = do
              lT <- encodeTransition [probPush, pendProbsLB ! (graphNode toG)] [pendProbsUB V.! (graphNode g)] tolVar
              uT <- encodeTransition [probPush, pendProbsUB ! (graphNode toG)] [pendProbsLB V.! (graphNode g)] touVar
              return [(lT, uT)]
            -- supports edges in the Support Graph
            maybePSupport = Set.lookupLE (Edge (graphNode toG) 0) $ supportEdges gn
            supportGn = suppGraph V.! (graphNode toG)
            leftContext = AugState (fst . semiconf $ gn) (phiNode g)
            rightContext = AugState (fst . semiconf $ supportGn) (phiNode toG)
            precRel stackSymbol qProps = (prec delta) stackSymbol qProps
            cDeltaPush (AugState (StateId _ q0 lab0) p0)  =  [ (AugState (StateId id1 q1 lab1) p1, prob_) |
                                  (q1, lab1, prob_) <- (deltaPush delta) q0
                                , p1 <- (phiDeltaPush delta) p0
                                , (precRel lab0 lab1 == Just Take) || lab1 == E.extractInput (bitenc delta) (current p1)
                                , let id1 = sIdMap StrictMap.! q1
                                ]
            cDeltaShift (AugState (StateId _ q0 lab0) p0) = [ (AugState (StateId id1 q1 lab1) p1, prob_) |
                                                              (q1, lab1, prob_) <- (deltaShift delta) q0
                                                            , p1 <- (phiDeltaShift delta) p0
                                                            , (precRel lab0 lab1 == Just Take) || lab1 == E.extractInput (bitenc delta) (current p1)
                                                            , let id1 = sIdMap StrictMap.! q1
                                                            ]
            cDeltaPop (AugState (StateId _ q0 _) p0) (AugState (StateId _ q1 _) p1)  = [(AugState (StateId id2 q2 lab2) p2, prob_) |
                                                                                          (q2, lab2, prob_) <- (deltaPop delta) q0 q1
                                                                                        ,  let id2 = sIdMap StrictMap.! q2
                                                                                        ,  p2 <- (phiDeltaPop delta) p0 p1]

            consistentFilter (AugState sId p0) = (getLabel sId) == E.extractInput (bitenc delta) (current p0)
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
              logDebugN $ "encountered a support transition - launching call to inner computation of fraction f for H node: " ++ show (gId g) ++ " to H node: " ++ show (gId toG)
              (lW, uW) <- GR.weightQuerySCC wGrobals sIdGen cDelta supports leftContext rightContext
              lT <- encodeTransition [lW, pendProbsLB V.! (graphNode toG)] [pendProbsUB V.! (graphNode g)] tolVar
              uT <- encodeTransition [uW, pendProbsUB V.! (graphNode toG)] [pendProbsLB V.! (graphNode g)] touVar
              return [(lT, uT)]
            cases
              | isJust maybePPush && to (fromJust maybePPush) == (graphNode toG) &&
                isJust maybePSupport && to (fromJust maybePSupport) == (graphNode toG) = do
                  pushEncs <- encodePushTrans
                  suppEncs <- encodeSupportTrans
                  return (pushEncs ++ suppEncs)
              | isJust maybePPush && to (fromJust maybePPush) == (graphNode toG) = encodePushTrans
              | isJust maybePSupport && to (fromJust maybePSupport) == (graphNode toG) = encodeSupportTrans
              | otherwise = error "there must be at least one edge in the support graph associated with this edge in graph H"
        cases

  in do
    -- a little sanity check
    unless (graphNode g == gnId gn) $ error "Encoding Push corresponding to non consistent pair GNode - graphNode"
    transitions <- mapM pushEnc fNodes
    lvar <- liftIO $ fromJust <$> HT.lookup lTypVarMap (gId g)
    uvar <- liftIO $ fromJust <$> HT.lookup uTypVarMap (gId g)
    lEq <- mkGe lvar =<< mkAdd (map fst . concat $ transitions)
    uEq <- mkLe uvar =<< mkAdd (map snd . concat $ transitions)
    -- debugging
    eqString <- astToString lEq
    logDebugN $ "Asserting Push/Support equation (lower bound): " ++ eqString
    eqString <- astToString uEq
    logDebugN $ "Asserting Push/Support equation (upper bound): " ++ eqString
    -- it's greater than zero for sure!
    lgtZero <- mkGt lvar =<< mkRational (0 :: Prob)
    ugtZero <- mkGt uvar =<< mkRational (0 :: Prob)
    lleqOne <- mkLe lvar =<< mkRational (1 :: Prob)
    uleqOne <- mkLe uvar =<< mkRational (1 :: Prob)
    soundness <- mkLe lvar uvar
    return [lEq, lgtZero, lleqOne, uEq, ugtZero, uleqOne, soundness]


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
  let fNodes = IntSet.toList . IntSet.filter (\idx -> isInH (gGraph V.! idx)) . Map.keysSet $ edges g
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
  transitions <- mapM shiftEnc fNodes
  lvar <- liftIO $ fromJust <$> HT.lookup lTypVarMap (gId g)
  uvar <- liftIO $ fromJust <$> HT.lookup uTypVarMap (gId g)
  lEq <- mkGe lvar =<< mkAdd (map fst transitions)
  uEq <- mkLe uvar =<< mkAdd (map snd transitions)
  -- debugging
  eqString <- astToString lEq
  logDebugN $ "Asserting Shift equation (lower bound): " ++ eqString
  eqString <- astToString uEq
  logDebugN $ "Asserting Shift equation (upper bound): " ++ eqString
  -- it's greater than zero for sure!
  lgtZero <- mkGt lvar =<< mkRational (0 :: Prob)
  ugtZero <- mkGt uvar =<< mkRational (0 :: Prob)
  lleqOne <- mkLe lvar =<< mkRational (1 :: Prob)
  uleqOne <- mkLe uvar =<< mkRational (1 :: Prob)
  soundness <- mkLe lvar uvar
  return [lEq, lgtZero, lleqOne, uEq, ugtZero, uleqOne, soundness]






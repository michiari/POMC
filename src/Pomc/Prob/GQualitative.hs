{- |
   Module      : Pomc.Prob.GQualitative
   Copyright   : 2026 Francesco Pontiggia
   License     : MIT
   Maintainer  : Francesco Pontiggia
-}

module Pomc.Prob.GQualitative ( qualitativeModelCheck
                              , dfs 
                              , addtoPath
                              ) where
import Pomc.LogUtils (MonadLogger, logInfoN)
import Pomc.SatUtil(freshPosId, freshNegId)
import Pomc.State(State(..))
import Pomc.Prec (Prec(..))
import Pomc.Potl(Formula(..))
import Pomc.PropConv(APType)
import qualified Pomc.Encoding as E
import Pomc.Z3T
import qualified Pomc.GStack as GS
import qualified Pomc.CustoMap as CM

import Pomc.Prob.GUtil
import Pomc.Prob.ProbUtils hiding (sIdMap, SIdGen)
import qualified Pomc.Prob.GReach as GR
import Pomc.Prob.SupportGraph(GraphNode(..), SupportGraph, TransitionInfo (..))
import Pomc.Prob.ProbEncoding(ProbEncodedSet)
import qualified Pomc.Prob.ProbEncoding as PE

import qualified Data.Strict.IntMap as StrictIntMap
import qualified Data.Strict.Map as StrictMap
import Data.IntMap(IntMap)
import qualified Data.IntMap as IntMap
import qualified Data.Set as Set
import Data.IntSet(IntSet)
import qualified Data.IntSet as IntSet
import Data.Hashable(Hashable)
import qualified Data.HashTable.ST.Basic as BH

import Data.List(partition)
import Data.Vector(Vector, (!))
import qualified Data.Vector as V
import Data.Bifunctor(first)
import Control.Monad.IO.Class (MonadIO)
import Control.Monad (when, forM_, foldM, forM)
import Control.Monad.ST (ST, RealWorld)

import Data.STRef (STRef, readSTRef, modifySTRef')
import Data.Maybe (fromJust, isNothing, mapMaybe)

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

    -- globals data structures for qualitative model checking
  let numPendingSemiconfs = foldl (flip ((+) . fromEnum)) 0 pendVector
  gGlobals <- liftSTtoIO $ newGGlobals numPendingSemiconfs
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
      newNode <- addtoPath gGlobals node (Internal 0 newId)
      _ <- dfs suppGraph gGlobals delta (pendVector V.!) True sIdMap newNode
      return ()

  -- some statistics about graph G
  idx <- liftSTtoIO $ readSTRef . idSeq $ gGlobals
  logInfoN $ "(The relevant portion of) Graph G has " ++ show idx ++ " nodes."
  liftSTtoIO $ modifySTRef' stats (\s -> s {gGraphSize = idx})

  -- returning whether there is a bottom SCC in H reachable from a not Phi initial node
  StrictIntMap.null <$> liftSTtoIO (readSTRef (bottomHSCCs gGlobals))

-- Gabow helpers
addtoPath :: GGlobals s pstate -> GNode -> HEdge -> ST s GNode
addtoPath gGlobals node edge  = do
  GS.push (sStack gGlobals) edge
  sSize <- GS.size $ sStack gGlobals
  CM.modify (gGraph gGlobals) (\g -> g{iValue = sSize}) (gId node)
  GS.push (bStack gGlobals) sSize
  return node{iValue = sSize}

-- contract the B stack, that represents the boundaries between SCCs on the current path
merge :: GGlobals s pstate -> Int -> ST s ()
merge gGlobals iVal = GS.popWhile_ (bStack gGlobals) (iVal <)
-- end Gabow helpers

reachPush :: (Ord pstate, Hashable pstate, Show pstate)
  => GGlobals s pstate -- global variables of the algorithm
  -> DeltaWrapper pstate
  -> SupportGraph pstate
  -> Bool
  -> (Int -> Bool) -- is a semiconf pending?
  -> StrictMap.Map pstate Int
  -> Int 
  -> StateId pstate
  -> State
  -> IntSet -- suppSet 
  -> IntMap Prob -- pushInfo
  -> ST s IntSet
reachPush gGlobals delta suppGraph fromPhi isPending sIdMap gnId_ q p suppSet pushMap =
  let fPushGns = map (first (suppGraph !)) . filter (isPending . fst) . IntMap.toList $ pushMap
      fSuppGns = map (suppGraph !) . filter isPending . IntSet.toList $ suppSet
      fPushPhiStates = (phiDeltaPush delta) p
      currentInput p_ = E.extractInput (bitenc delta) (current p_)
      fPushGnodes =
        [(prob_, gn1, p1) |
            (gn1, prob_) <- fPushGns, p1 <- fPushPhiStates
          , (getLabel . fst . semiconf $ gn1) == currentInput p1
        ]
      -- for exploring supports
      precRel = prec delta
      leftContext = AugState q p
      cDeltaPush (AugState (StateId _ q0 lab0) p0)  =
        [AugState (StateId id1 q1 lab1) p1 |
            (q1, lab1, _) <- (deltaPush delta) q0
          , p1 <- (phiDeltaPush delta) p0
          , (precRel lab0 lab1 == Just Take) || lab1 == currentInput p1
          , let id1 = sIdMap StrictMap.! q1
        ]
      cDeltaShift (AugState (StateId _ q0 lab0) p0) =
        [ AugState (StateId id1 q1 lab1) p1 |
            (q1, lab1, _) <- (deltaShift delta) q0
          , p1 <- (phiDeltaShift delta) p0
          , (precRel lab0 lab1 == Just Take) || lab1 == currentInput p1
          , let id1 = sIdMap StrictMap.! q1
        ]
      cDeltaPop (AugState (StateId _ q0 _) p0) (AugState (StateId _ q1 _) p1)  =
        [AugState (StateId id2 q2 lab2) p2 |
            (q2, lab2, _) <- (deltaPop delta) q0 q1
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
    fromId <- fromJust <$> BH.lookup (ggraphMap gGlobals) (gnId_, p)
    -- handling support edges
    fSuppAugStates <- if not . null $ fSuppGns
                        then GR.reachableStates (grGlobals gGlobals) cDelta leftContext
                        else return []
    -- a sanity check
    -- unless (all (consistentFilter. fst) fSuppAugStates) $ error "a support Augmented State is inconsistent"
    let fSuppGnodes =
          [(gn1, p1, suppSatSet) |
            gn1 <- fSuppGns
            , (AugState (StateId _ q1 _) p1, suppSatSet) <- fSuppAugStates
            , (getState . fst . semiconf $ gn1) == q1
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
  -> Int
  -> State
  -> IntMap Prob
  -> ST s IntSet
reachShift gGlobals delta suppGraph fromPhi isPending sIdMap gnId_ p shiftMap =
  let fGns = map (first (suppGraph !)) . filter (isPending . fst) . IntMap.toList $ shiftMap
      fPhiStates = (phiDeltaShift delta) p
      fGnodes =
        [(prob_, gn1, p1) |
          (gn1, prob_) <- fGns, p1 <- fPhiStates,
          (getLabel . fst . semiconf $ gn1) == E.extractInput (bitenc delta) (current p1)
        ]
  in do
    fromId <- fromJust <$> BH.lookup (ggraphMap gGlobals) (gnId_, p)
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
            -- I need to push anyway because I want to keep track of cycles in createComponent,
            -- and because it might be a support edge determining acceptance
            | iValue nextNode > 0  = GS.push (sStack gGlobals) e >> merge gGlobals (iValue nextNode) >> return IntSet.empty
            | otherwise = error "unreachable error"
      cases)

dfs :: (Ord pstate, Hashable pstate, Show pstate)
  => SupportGraph pstate
  -> GGlobals s pstate
  -> DeltaWrapper pstate
  -> (Int -> Bool) -- is a semiconf pending?
  -> Bool
  -> StrictMap.Map pstate Int
  -> GNode -- current gnode
  -> ST s IntSet
dfs suppGraph gGlobals delta isPending fromPhi sIdMap gnode =
  let gn = suppGraph ! (graphNode gnode)
      p = phiNode gnode
      (q,_) = semiconf gn
      -- this case includes the initial push
      buildCases (Push suppSet pushMap) = reachPush gGlobals delta suppGraph fromPhi isPending sIdMap (gnId gn) q p suppSet pushMap
      buildCases (Shift shiftMap) = reachShift gGlobals delta suppGraph fromPhi isPending sIdMap (gnId gn) p shiftMap
      buildCases (Pop _) =  error
        $ "A pop transition cannot be reached in the augmented graph of pending semiconfs, as it terminates almost surely: " ++ show gn
  in do
    descendantSCCs <- buildCases (gnEdges gn)
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
          filtDescs <- deleteDescendants gGlobals sccSemiconfs descendantSCCs
          -- check if current SCC is a candidate bottom SCC of H
          let isBott = isBottom suppGraph sccSemiconfs isPending
          isAccept <- isAccepting gGlobals delta sccEdges
          if isBott && isAccept
            then do
              newSCCId <- freshNegId (cGabow gGlobals)
              modifySTRef' (bottomHSCCs gGlobals) $ StrictIntMap.insert newSCCId sccSemiconfs
              let newDescs = IntSet.insert newSCCId filtDescs
              forM_ sccEdges $ \e -> CM.modify (gGraph gGlobals) (\g_ -> g_{iValue = newSCCId, descSccs = newDescs}) (toG e)
              return newDescs
            else do
              forM_ sccEdges $ \e -> CM.modify (gGraph gGlobals) (\g_ -> g_{iValue = -1, descSccs = filtDescs}) (toG e)
              return filtDescs
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
      checkTransitions (Push suppSet pushMap) = (bottomCheck . IntMap.keys) pushMap && (bottomCheck . IntSet.elems) suppSet
      checkTransitions (Shift shiftMap) = (bottomCheck . IntMap.keys) shiftMap
      checkTransitions (Pop _) = error "Pop Semiconfs cannot occurr in graph G."
  in all (checkTransitions . gnEdges) gns

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
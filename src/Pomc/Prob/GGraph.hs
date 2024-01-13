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

import Pomc.Prob.ProbUtils hiding (SIdGen)
import Pomc.SatUtil(SIdGen, SatState(..))
import Pomc.TimeUtils (startTimer, stopTimer)
import qualified Pomc.SatUtil as SU
import Pomc.State(State(..), Input)
import Pomc.Prec (Prec(..))
import Pomc.Potl(Formula(..))
import Pomc.PropConv(APType)
import Pomc.Check (EncPrecFunc)

import Pomc.GStack(GStack)
import qualified Pomc.GStack as GS

import qualified Pomc.CustoMap as CM

import qualified Pomc.Prob.GReach as GR
import Pomc.Prob.GReach(GRobals (suppEnds), weightQuerySCC)

import Pomc.Prob.SupportGraph(GraphNode(..), Edge(..), SupportGraph)

import Pomc.Prob.ProbEncoding(ProbEncodedSet)
import qualified Pomc.Prob.ProbEncoding as PE

import qualified Pomc.IOSetMap as IOSM

import qualified Pomc.IOStack as IOGS

import qualified Pomc.Encoding as E

import Pomc.Prob.FixPoint(VarKey)

import Data.IntMap.Strict(IntMap)
import qualified Data.IntMap.Strict as Map

import Data.Map(Map)
import qualified Data.Map as GeneralMap

import Data.Set(Set)
import qualified Data.Set as Set

import Data.IntSet(IntSet)
import qualified Data.IntSet as IntSet

import qualified Data.Vector.Mutable as MV

import Control.Monad.IO.Class (MonadIO(liftIO))
import Control.Monad(when, unless, forM_, foldM, forM)
import Control.Monad.ST (ST, stToIO)
import Control.Monad.ST (RealWorld)

import Data.STRef (STRef, newSTRef, readSTRef, modifySTRef')
import Data.Maybe (fromJust, isNothing, isJust, mapMaybe)

import GHC.Generics (Generic)
import Data.Hashable
import qualified Data.HashTable.IO as HT
import qualified Data.HashTable.ST.Basic as BH

import qualified Data.Vector.Mutable as MV
import Data.Vector(Vector)
import qualified Data.Vector as V

import Z3.Monad

import qualified Debug.Trace as DBG
import GHC.IO (ioToST)
import Data.IORef (newIORef, modifyIORef', readIORef)
import Data.Scientific (Scientific)

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
data AugState pstate =  AugState pstate Input State deriving (Generic, Eq, Show, Ord)

instance Hashable s => Hashable (AugState s)

instance SatState (AugState s) where
  getSatState (AugState _ _ p) = p
  {-# INLINABLE getSatState #-}

  -- always promote the phi state
  getStateProps _ (AugState _ lab _) = lab
  {-# INLINABLE getStateProps #-}

-- the G Graph computed by this function
type GGraph s = CM.CustoMap s GNode

-- the global variables in the algorithm for constructing graph G
data GGlobals s pstate = GGlobals
  { idSeq      :: STRef s Int
  , ggraphMap   :: HashTable s (Int, State) Int
  , gGraph      :: STRef s (GGraph s)
  , grGlobals   :: GRobals s (AugState pstate)
  }

-- requires: the initial semiconfiguration has id 0
-- requires: idSeq is at 0
-- pstate: a parametric type for states of the input popa
buildGGraph :: (Ord pstate, Hashable pstate, Show pstate)
                => GGlobals s pstate
                -> DeltaWrapper pstate
                -> [State] -- initial states of the phiOpa 
                -> (Int -> ST s (GraphNode pstate)) -- getter for retrieving a graphNode associated with the given int
                -> (Int -> Bool) -- is a semiconf pending?
                -> ST s (GGraph s, Int)
buildGGraph gglobals delta phiInitials getGn isPending = do
  iniGn <- getGn 0
  let iniLabel = getLabel . fst . semiconf $ iniGn
  currentIdSeq <- readSTRef $ idSeq gglobals
  when (currentIdSeq /= 0) $ error "memory found containing some trash values when building graph G"
  filtered <- foldM (\acc s ->
                      if iniLabel == E.extractInput (bitenc delta) (current s)
                        then do
                          -- create a new GNode 
                          newId <- freshPosId (idSeq gglobals)
                          BH.insert (ggraphMap gglobals) (gnId iniGn, s) newId
                          CM.insert (gGraph gglobals) newId
                            $ GNode {gId= newId, graphNode = gnId iniGn, phiNode = s, edges = Map.empty, iValue = 0, descSccs = IntSet.empty}
                          return (s:acc)
                        else return acc
                    )
                    []
                    phiInitials
  initialNodesBound <- readSTRef . idSeq $ gglobals
  forM_ filtered $ \s -> build gglobals delta getGn isPending (iniGn, s)
  idx <- readSTRef . idSeq $ gglobals
  g <- CM.take idx <$> readSTRef (gGraph gglobals)
  return (g, initialNodesBound)

build :: (Ord pstate, Hashable pstate, Show pstate)
          => GGlobals s pstate -- global variables of the algorithm
          -> DeltaWrapper pstate
          -> (Int -> ST s (GraphNode pstate)) -- getter for retrieving a graphNode associated with the given int
          -> (Int -> Bool) -- is a semiconf pending?
          -> (GraphNode pstate, State) -- current GNode
          -> ST s ()
build gglobals delta getGn isPending (gn, p) = do
  let
    (q,g) = semiconf gn
    precRel = (prec delta) (fst . fromJust $ g) (getLabel q)
    cases
      -- a sanity check
      | getLabel q /= E.extractInput (bitenc delta) (current p) = error "inconsistent GNode when building the G Graph"

      -- this case includes the initial push
      | (isNothing g) || precRel == Just Yield =
        buildPush gglobals delta getGn isPending (gn,p)

      | precRel == Just Equal =
        buildShift gglobals delta getGn isPending (gn, p)

      | precRel == Just Take = error $ "a pop transition cannot be reached in the augmented graph of pending semiconfs, as it terminates almost surely" ++ show gn
      | otherwise = return ()
  cases


buildPush :: (Ord pstate, Hashable pstate, Show pstate)
              => GGlobals s pstate -- global variables of the algorithm
              -> DeltaWrapper pstate
              -> (Int -> ST s (GraphNode pstate)) -- getter for retrieving a graphNode associated with the given int
              -> (Int -> Bool) -- is a semiconf pending?
              -> (GraphNode pstate, State) -- current gnode
              -> ST s ()
buildPush gglobals delta getGn isPending (gn, p) =
  let fPendingPushSemiconfs = Set.toList . Set.filter isPending . Set.map to $ internalEdges gn
      fPendingSuppSemiconfs = Set.toList . Set.filter isPending . Set.map to $ supportEdges gn
      fPushPhiStates = (phiDeltaPush delta) p
  in do
    -- handling the push edges
    fPushGns <- mapM getGn fPendingPushSemiconfs
    let fPushGnodes = [(gn1, p1) | gn1 <- fPushGns, p1 <- fPushPhiStates, (getLabel . fst . semiconf $ gn1) == E.extractInput (bitenc delta) (current p1)]
    forM_ fPushGnodes $ \(gn1, p1) -> buildEdge gglobals delta getGn isPending (gn, p) (PE.empty . proBitenc $ delta) (gn1, p1)
    -- handling the support edges
    fSuppGns <- mapM getGn fPendingSuppSemiconfs
    let leftContext = AugState (getState . fst . semiconf $ gn) (getLabel . fst . semiconf $ gn) p
        cDeltaPush (AugState q0 _ p0)  =  [ (AugState q1 lab p1, prob_) |
                                            (q1, lab, prob_) <- (deltaPush delta) q0
                                          , p1 <- (phiDeltaPush delta) p0
                                          ]
        cDeltaShift (AugState q0 _ p0) =  [ (AugState q1 lab p1, prob_) |
                                            (q1, lab, prob_) <- (deltaShift delta) q0
                                          , p1 <- (phiDeltaShift delta) p0
                                          ]
        cDeltaPop (AugState q0 _ p0) (AugState q1 _ p1)  = [ (AugState q2 lab p2, prob_) |
                                                             (q2, lab, prob_) <- (deltaPop delta) q0 q1
                                                           , p2 <- (phiDeltaPop delta) p0 p1
                                                           ]

        consistentFilter (AugState _ lab p0) = lab == E.extractInput (bitenc delta) (current p0)
        cDelta = GR.Delta
          { GR.bitenc = bitenc delta
          , GR.proBitenc = proBitenc delta
          , GR.prec   = prec delta
          , GR.deltaPush = cDeltaPush
          , GR.deltaShift = cDeltaShift
          , GR.deltaPop = cDeltaPop
          , GR.consistentFilter = consistentFilter
          }
    fSuppAugStates <- if not . null $ fSuppGns
                        then  GR.reachableStates (grGlobals gglobals) cDelta leftContext
                        else return []
    let fSuppGnodes = [(gn1, p1, suppSatSet) |
                        gn1 <- fSuppGns
                      , (AugState q lab p1, suppSatSet) <- fSuppAugStates
                      , (getState . fst . semiconf $ gn1) == q
                      , consistentFilter (AugState q lab p1)
                      ]
    forM_ fSuppGnodes $ \(gn1, p1, suppSatSet) -> buildEdge gglobals delta getGn isPending (gn, p) suppSatSet (gn1, p1)

buildShift :: (Ord pstate, Hashable pstate, Show pstate)
               => GGlobals s pstate -- global variables of the algorithm
               -> DeltaWrapper pstate
               -> (Int -> ST s (GraphNode pstate)) -- getter for retrieving a graphNode associated with the given int
               -> (Int -> Bool) -- is a semiconf pending?
               -> (GraphNode pstate, State) -- current GNopde
               -> ST s ()
buildShift gglobals delta getGn isPending (gn, p) =
  let fPendingSemiconfs = Set.toList . Set.filter isPending . Set.map to $ internalEdges gn
      fPhiStates = (phiDeltaShift delta) p
  in do
    -- just a sanity check
    unless (Set.null . supportEdges $ gn) $ error "a shift semiconf cannot have summaries"
    fGns <- mapM getGn fPendingSemiconfs
    let fGnodes = [(gn1, p1) | gn1 <- fGns, p1 <- fPhiStates, (getLabel . fst . semiconf $ gn1) == E.extractInput (bitenc delta) (current p1)]
    forM_ fGnodes $ \(gn1, p1) -> buildEdge gglobals delta getGn isPending (gn, p) (PE.empty . proBitenc $ delta) (gn1, p1)

-- decomposing an edge to a new node
buildEdge :: (Ord pstate, Hashable pstate, Show pstate)
                 => GGlobals s pstate -- global variables of the algorithm
                 -> DeltaWrapper pstate
                 -> (Int -> ST s (GraphNode pstate)) -- getter for retrieving a graphNode associated with the given int
                 -> (Int -> Bool) -- is a semiconf pending?
                 -> (GraphNode pstate, State) -- current node
                 -> ProbEncodedSet -- for formulae satisfied in a support
                 -> (GraphNode pstate, State) -- to node
                 -> ST s ()
buildEdge gglobals delta getGn isPending (gn, p) suppSatSet (gn1, p1) =
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
    when (isNothing maybeId) $ build gglobals delta getGn isPending (gn1, p1)

-------- finding the bottom SCCs of subgraph H -------------
type GraphNodesSCC = IntSet

data HGlobals s pstate = HGlobals
  { graph :: GGraph s
  , supportGraph :: SupportGraph s pstate
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
qualitativeModelCheck :: (Ord pstate, Hashable pstate, Show pstate)
                      => DeltaWrapper pstate
                      -> Formula APType -- phi: input formula to check
                      -> [State] -- initial states of the phiOpa 
                      -> SupportGraph s pstate
                      -> Vector Bool
                      -> ST s Bool
qualitativeModelCheck delta phi phiInitials suppGraph pendVector = do
  -- global data structures for constructing graph G
  newIdSequence <- newSTRef (0 :: Int)
  emptyGGraphMap <- BH.new
  emptyGGraph <- CM.empty
  emptyGRGlobals <-  GR.newGRobals
  let gGlobals = GGlobals { idSeq = newIdSequence
                            , ggraphMap = emptyGGraphMap
                            , gGraph = emptyGGraph
                            , grGlobals = emptyGRGlobals
                          }

  (g, iniCount) <- buildGGraph gGlobals delta phiInitials (MV.unsafeRead suppGraph) (pendVector V.!)
  -- globals data structures for qualitative model checking
  -- -1 is reserved for useless (i.e. single node) SCCs
  sccCounter <- newSTRef (-2 :: Int)
  newSS         <- GS.new
  newBS         <- GS.new
  newFoundSCCs <- newSTRef Map.empty
  let hGlobals = HGlobals { graph = g
                          , supportGraph = suppGraph
                          , sStack = newSS
                          , bStack = newBS
                          , cGabow = sccCounter
                          , bottomHSCCs = newFoundSCCs
                          }
  (phiNodes, notPhiNodes) <- foldM
    (\(pn, npn) i -> do
      node <- MV.unsafeRead g i
      if E.member (bitenc delta) phi . current . phiNode $ node
        then return (i:pn, npn)
        else return (pn, i:npn)
    )
    ([],[])
    [0.. (iniCount -1)]

  -- explore nodes where phi does not hold
  forM_ notPhiNodes $ \i -> do
    node <- MV.unsafeRead g i
    when (iValue node == 0) $
      addtoPath hGlobals node (Internal (gId node)) >>= dfs hGlobals delta (pendVector V.!) False >> return ()
  -- explore nodes where phi does hold
  forM_ phiNodes $ \i -> do
    node <- MV.unsafeRead g i
    nullCandidates <- Map.null <$> readSTRef (bottomHSCCs hGlobals)
    when (iValue node == 0 && not nullCandidates) $
      addtoPath hGlobals node (Internal (gId node)) >>= dfs hGlobals delta (pendVector V.!) True >> return ()
  -- returning whether there is a bottom SCC in H reachable from a not Phi initial node
  Map.null <$> readSTRef (bottomHSCCs hGlobals)

dfs :: HGlobals s pstate
      -> DeltaWrapper pstate
      -> (Int -> Bool) -- is a semiconf pending?
      -> Bool
      -> GNode
      -> ST s IntSet
dfs hGlobals delta isPending fromPhi g =
  let
    -- creating an edge to push on the stack
    encodeEdge ident sss
        | PE.null sss = Internal ident
        | otherwise = Support ident sss
    -- different cases of the Gabow SCC algorithm
    cases e nextNode
      | (iValue nextNode == 0) = addtoPath hGlobals nextNode e >>= dfs hGlobals delta isPending fromPhi
      | (iValue nextNode < 0)  = return (descSccs nextNode)
      -- I need to push anyway because I want to keep track of cycles in createComponent
      | (iValue nextNode > 0)  = GS.push (sStack hGlobals) e >> merge hGlobals nextNode >> return IntSet.empty
      | otherwise = error "unreachable error"
  in do
    descendantSCCs <-  forM (Map.toList $ edges g)
                      $ \(ident, sss) ->  MV.unsafeRead (graph hGlobals) ident >>= cases (encodeEdge ident sss)
    if fromPhi
      then createComponentPhi hGlobals g (IntSet.unions descendantSCCs)
      else createComponent hGlobals delta isPending g (IntSet.unions descendantSCCs)


createComponent :: HGlobals s pstate -> DeltaWrapper pstate -> (Int -> Bool) -> GNode -> IntSet -> ST s IntSet
createComponent hGlobals delta isPending g descendantSCCs = do
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
          isBott <- isBottom hGlobals sccSemiconfs isPending
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
  -- returning filtered descendant
  (\m -> IntSet.filter (`Map.member` m) descendants) <$> readSTRef (bottomHSCCs hGlobals)

-- first necessary condition for an SCC to be in H
isBottom :: HGlobals s pstate -> IntSet -> (Int -> Bool) -> ST s Bool
isBottom hGlobals suppGraphSCC isPending = do
  gns <- forM (IntSet.toList suppGraphSCC) $ MV.unsafeRead (supportGraph hGlobals)
  let checkInternals = all (\e -> IntSet.member (to e) suppGraphSCC) . Set.filter (isPending . to) . internalEdges
      checkSupports  = all (\e -> IntSet.member (to e) suppGraphSCC) . Set.filter (isPending . to) . supportEdges
  return $ all (\gn -> checkInternals gn && checkSupports gn) gns

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
quantitativeModelCheck :: (Ord pstate, Hashable pstate, Show pstate)
                      => DeltaWrapper pstate
                      -> Formula APType -- phi: input formula to check
                      -> [State] -- initial states of the phiOpa 
                      -> SupportGraph RealWorld pstate
                      -> IntSet
                      -> Map VarKey Prob
                      -> Map VarKey Prob
                      -> ST RealWorld (Prob, Prob, Stats)
quantitativeModelCheck delta phi phiInitials suppGraph asTermSemiconfs lowerBounds upperBounds = do
  -- global data structures for constructing graph G
  newIdSequence <- newSTRef (0 :: Int)
  emptyGGraphMap <- BH.new
  emptyGGraph <- CM.empty
  emptyGRGlobals <-  GR.newGRobals
  let gGlobals = GGlobals { idSeq = newIdSequence
                            , ggraphMap = emptyGGraphMap
                            , gGraph = emptyGGraph
                            , grGlobals = emptyGRGlobals
                          }
  (computedGraph, iniCount) <- buildGGraph gGlobals delta phiInitials (MV.unsafeRead suppGraph) (\i -> not $ IntSet.member i asTermSemiconfs)
  -- globals data structures for qualitative model checking
  -- -1 is reserved for useless (i.e. single node) SCCs
  sccCounter <- newSTRef (-2 :: Int)
  newSS         <- GS.new
  newBS         <- GS.new
  newFoundSCCs <- newSTRef Map.empty
  let hGlobals = HGlobals { graph = computedGraph
                          , supportGraph = suppGraph
                          , sStack = newSS
                          , bStack = newBS
                          , cGabow = sccCounter
                          , bottomHSCCs = newFoundSCCs
                          }

  
  -- computing all the bottom SCCs of graph H
  phiInitialGNodesIdxs <- foldM (\acc idx -> do
    node <- MV.unsafeRead computedGraph idx
    when (iValue node == 0) $
      addtoPath hGlobals node (Internal (gId node)) >>= dfs hGlobals delta (\i -> not $ IntSet.member i asTermSemiconfs) False >> return ()
    if E.member (bitenc delta) phi . current . phiNode $ node
      then return (idx:acc)
      else return acc
    )
    []
    [0.. (iniCount -1)]

  hSCCs <- Map.keysSet <$> readSTRef (bottomHSCCs hGlobals)

  DBG.traceM $ "Computed qualitative model checking: "
  bottomString <- show <$> readSTRef (bottomHSCCs hGlobals)
  gString <- CM.showMap computedGraph

  DBG.traceM gString
  DBG.traceM bottomString

  -- computing the probability of termination
  let isInH g = not . IntSet.null . IntSet.intersection hSCCs $ descSccs g
      lowerBoundsMap = Map.fromListWith (+) . map (\(k, p) -> (fst k, p)) . GeneralMap.toList $ lowerBounds
      upperBoundsMap = Map.fromListWith (+) . map (\(k, p) -> (fst k, p)) . GeneralMap.toList $ upperBounds

      pendProbsUpperBounds = V.generate (MV.length suppGraph) (\idx -> 1 - Map.findWithDefault 0 idx lowerBoundsMap)
      pendProbsLowerBounds = V.generate (MV.length suppGraph) (\idx -> 1 - Map.findWithDefault 0 idx upperBoundsMap)

      insert var Nothing         = (Just [var], ())
      insert var (Just old_vars) = (Just (var:old_vars), ())


  -- freezing makes coding easier
  freezedGGraph <- V.freeze computedGraph
  freezedSuppGraph <- V.freeze suppGraph

  let boolVec = V.map isInH freezedGGraph

  DBG.traceM $ show boolVec

  newlMap <- BH.new
  newlGroupedMap <- BH.new

  newuMap <- BH.new
  newuGroupedMap <- BH.new


  ioToST $ evalZ3With (Just QF_LRA) stdOpts $ do

    -- generate all variables and add them to two hashtables
    forM_ freezedGGraph $ \g -> when (isInH g) $ do
      newlVar <- mkFreshRealVar (show (gId g) ++ "L")
      newuVar <- mkFreshRealVar (show (gId g) ++ "U")
      liftIO $ HT.insert newlMap (gId g) newlVar
      liftIO $ HT.insert newuMap (gId g) newuVar
      liftIO $ HT.mutate newlGroupedMap (graphNode g) (insert newlVar)
      liftIO $ HT.mutate newuGroupedMap (graphNode g) (insert newuVar)

    DBG.traceM "Generated z3 vars for encoding (2)"
    newMapString <- show <$> liftIO (HT.toList newlMap)
    newGroupedMapString <- show <$> liftIO (HT.toList newlGroupedMap)

    DBG.traceM $ "New map: " ++ newMapString
    DBG.traceM $ "New grouped map: " ++ newGroupedMapString

    -- preparing the global variables for the computation of the fractions f
    freezedSuppEnds <- liftIO $ GR.freezeSuppEnds (grGlobals gGlobals)

    newIdSeq <- liftIO $ newIORef 0
    newGraphMap <-  liftIO $ HT.new
    newFVarMap <- liftIO $ IOSM.empty
    newSStack <- liftIO $ IOGS.new
    newBStack <- liftIO $ IOGS.new
    newIVector <- liftIO $ HT.new
    newScntxs <- liftIO $ HT.new
    newCannotReachPop <- liftIO $ newIORef IntSet.empty
    newLowerEqMap <- liftIO $ HT.new
    newUpperEqMap <- liftIO $ HT.new
    newEps <- liftIO $ newIORef defaultTolerance
    newStats <- liftIO . newIORef $ Stats 0 0 0 0

    let globals = GR.WeightedGRobals { GR.idSeq = newIdSeq
                                     , GR.graphMap = newGraphMap
                                     , GR.varMap  = newFVarMap
                                     , GR.sStack = newSStack
                                     , GR.bStack = newBStack
                                     , GR.iVector = newIVector
                                     , GR.successorsCntxs = newScntxs
                                     , GR.cannotReachPop = newCannotReachPop
                                     , GR.lowerEqMap = newLowerEqMap
                                     , GR.upperEqMap = newUpperEqMap
                                     , GR.actualEps = newEps
                                     , GR.stats = newStats
                                     }

    DBG.traceM "Encoding conditions (2b) and (2c)"
    -- encodings (2b) and (2c)
    (encs1) <- foldM
      (\(acc) gNode ->
          if isInH gNode
            then do
              (newEncs) <- encode globals (GR.sIdGen (grGlobals gGlobals)) freezedSuppEnds delta (newlMap, newuMap) freezedSuppGraph freezedGGraph (prec delta) isInH gNode pendProbsLowerBounds pendProbsUpperBounds lowerBounds upperBounds
              return (newEncs ++ acc)
            else return (acc)
      )
      []
      freezedGGraph

    DBG.traceM "Encoding conditions (2a)"
    -- encoding (2a)
    groupedlMaptoList <- liftIO (HT.toList newlGroupedMap)
    encs2 <- foldM (\(acc) (_, vList) -> do
        vSum <- mkAdd vList
        lConstr1 <- mkLe vSum =<< mkRational (1 :: Prob)
        lConstr2 <- mkGe vSum =<< mkRational (1 - defaultRTolerance)
        return (lConstr1:lConstr2:acc)
      )
      []
      groupedlMaptoList

    groupeduMaptoList <- liftIO (HT.toList newuGroupedMap)
    encs3 <- foldM (\(acc) (_, vList) -> do
          vSum <- mkAdd vList
          uConstr1 <- mkGe vSum =<< mkRational (1 :: Prob)
          uConstr2 <- mkLe vSum =<< mkRational (1 + defaultRTolerance)
          return (uConstr1:uConstr2:acc)
        )
        []
        groupeduMaptoList

    -- computing a lower bound on the probability to satisfy the given property
    philVars <- liftIO $ foldM  (\acc idx -> 
        if isInH (freezedGGraph V.! idx)
          then do
            var <- fromJust <$> HT.lookup newlMap idx
            return (var:acc)
          else return acc
        ) [] phiInitialGNodesIdxs
    
    phiuVars <- liftIO $ foldM  (\acc idx -> 
          if isInH (freezedGGraph V.! idx)
            then do
              var <- fromJust <$> HT.lookup newuMap idx
              return (var:acc)
            else return acc
          ) [] phiInitialGNodesIdxs

    sumlVar <- mkAdd philVars
    sumuVar <- mkAdd phiuVars

    startSol <- startTimer
    mapM_ assert encs1 >> mapM_ assert encs2 >> mapM_ assert encs3
    (lb, ub) <- fromJust . snd <$> withModel (\model -> do
      mString <- modelToString model
      DBG.traceM $ "Computed model(Lower and upper bound): " ++ mString
      sumlEq <- astToString sumlVar
      DBG.traceM $ "The probability of satisfying phi is given by sum: " ++ sumlEq
      l <- astToString . fromJust =<< eval model sumlVar
      u <- astToString . fromJust =<< eval model sumuVar
      DBG.traceM $ "Computed lower bound on the quantitative probability: " ++ show l
      DBG.traceM $ "Computed upper bound on the quantitative probability: " ++ show u
      return $ (toRational (read (takeWhile (/= '?') l) :: Scientific), toRational (read (takeWhile (/= '?') u) :: Scientific)))

    tSol <- stopTimer startSol ub
    allStats <- (\s -> s { quantSolTime = quantSolTime s + tSol}) <$> liftIO (readIORef (GR.stats globals))

    return (lb, ub, allStats)

  -- helpers for the Z3 encoding

-- every node of graph H is associated with a Z3 var
type TypicalVarKey = Int
type TypicalVarMap = HT.BasicHashTable Int AST


encodeTransition :: [Prob] -> AST -> Z3 AST
encodeTransition probs toVar = do
  normalizedProbs <- mapM mkRational probs
  mkMul $ normalizedProbs ++ [toVar]

encode :: (Ord pstate, Hashable pstate, Show pstate)
      => GR.WeightedGRobals (AugState pstate) 
      -> SIdGen RealWorld (AugState pstate)
      -> Vector (Set(SU.StateId (AugState pstate)))
      -> DeltaWrapper pstate
      -> (TypicalVarMap, TypicalVarMap)
      -> Vector (GraphNode pstate)
      -> Vector GNode
      -> EncPrecFunc
      -> (GNode -> Bool)
      -> GNode
      -> Vector Prob
      -> Vector Prob
      -> Map VarKey Prob
      -> Map VarKey Prob
      -> Z3 ([AST])
encode wGrobals sIdGen supports delta (lTypVarMap, uTypVarMap) suppGraph gGraph precFun isInH gNode pendProbsLB pendProbsUB lowerBs upperBs = do
  let gn = suppGraph V.! (graphNode gNode)
      (q,g) = semiconf gn
      qLabel = getLabel q
      precRel = precFun (fst . fromJust $ g) qLabel -- safe due to laziness
      cases
        -- this case includes the initial push
        | isNothing g || precRel == Just Yield =
            encodePush wGrobals sIdGen supports delta (lTypVarMap, uTypVarMap) suppGraph gGraph isInH gNode gn pendProbsLB pendProbsUB lowerBs upperBs

        | precRel == Just Equal =
            encodeShift (lTypVarMap, uTypVarMap) gGraph isInH gNode gn pendProbsLB pendProbsUB

        | otherwise = fail "unexpected prec rel"
  --DBG.traceM $ "Encoding gNode: " ++ show gNode
  --DBG.traceM $ "Corresponding semiconf: " ++ show gn
  cases

-- encoding helpers --
encodePush :: (Ord pstate, Hashable pstate, Show pstate)
  => GR.WeightedGRobals (AugState pstate) 
  -> SIdGen RealWorld (AugState pstate)
  -> Vector (Set(SU.StateId (AugState pstate)))
  -> DeltaWrapper pstate
  -> (TypicalVarMap, TypicalVarMap)
  -> Vector (GraphNode pstate)
  -> Vector GNode
  -> (GNode -> Bool)
  -> GNode
  -> GraphNode pstate
  -> Vector Prob
  -> Vector Prob
  -> Map VarKey Prob
  -> Map VarKey Prob
  -> Z3 ([AST])
encodePush wGrobals sIdGen supports delta (lTypVarMap, uTypVarMap) suppGraph gGraph isInH g gn pendProbsLB pendProbsUB lowerBs upperBs =
  let fNodes = IntSet.toList . IntSet.filter (\idx -> isInH (gGraph V.! idx)) . Map.keysSet $ edges g
      pushEnc toIdx = do
        tolVar <- liftIO $ fromJust <$> HT.lookup lTypVarMap toIdx
        touVar <- liftIO $ fromJust <$> HT.lookup uTypVarMap toIdx
        DBG.traceM $ "Encoding transition to " ++ show toIdx
        -- a small trick to be refactored later (itneed a lot of boring refactoring...)
        let toG =gGraph V.! toIdx
            maybePInternal = Set.lookupLE (Edge (graphNode toG) 0) $ internalEdges gn
            maybePSummary = Set.lookupLE (Edge (graphNode toG) 0) $ supportEdges gn
            cases
              | isJust maybePInternal && to (fromJust maybePInternal) == (graphNode toG) =
                  let p = (prob $ fromJust maybePInternal)
                      normalizedLP = p * (pendProbsLB V.! (graphNode toG)) / ( pendProbsUB V.! (graphNode g))
                      normalizedUP = p * (pendProbsUB V.! (graphNode toG)) / ( pendProbsLB V.! (graphNode g))
                  in do
                    DBG.traceM $ "It corresponds to a push transition"
                    lT <- encodeTransition [normalizedLP] tolVar
                    uT <- encodeTransition [normalizedUP] touVar
                    return (lT, uT)

              | isJust maybePSummary && to (fromJust maybePSummary) == (graphNode toG) = 
                  let supportGn = suppGraph V.! (graphNode toG)
                      supportState = getId . fst . semiconf $ supportGn
                      --lP =  Set.foldl (+) 0 $ Set.map (\e -> (prob e) * (lowerBs GeneralMap.! (to e, supportState))) (internalEdges gn)
                      --uP =  Set.foldl (+) 0 $ Set.map (\e -> (prob e) * (upperBs GeneralMap.! (to e, supportState))) (internalEdges gn)
                      leftContext = AugState (getState . fst . semiconf $ gn) (getLabel . fst . semiconf $ gn) (phiNode g)
                      rightContext = AugState (getState . fst . semiconf $ supportGn) (getLabel . fst . semiconf $ supportGn) (phiNode toG)
                      cDeltaPush (AugState q0 _ p0)  =  [ (AugState q1 lab p1, prob_) |
                                            (q1, lab, prob_) <- (deltaPush delta) q0
                                          , p1 <- (phiDeltaPush delta) p0
                                          ]
                      cDeltaShift (AugState q0 _ p0) =  [ (AugState q1 lab p1, prob_) |
                                            (q1, lab, prob_) <- (deltaShift delta) q0
                                          , p1 <- (phiDeltaShift delta) p0
                                          ]
                      cDeltaPop (AugState q0 _ p0) (AugState q1 _ p1)  = [ (AugState q2 lab p2, prob_) |
                                                             (q2, lab, prob_) <- (deltaPop delta) q0 q1
                                                           , p2 <- (phiDeltaPop delta) p0 p1
                                                           ]

                      consistentFilter (AugState _ lab p0) = lab == E.extractInput (bitenc delta) (current p0)
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
                    DBG.traceM $ "It corresponds to a support transition - launching call to inner computation of fraction f"
                    (lW, uW) <- liftIO $ weightQuerySCC wGrobals sIdGen cDelta supports leftContext rightContext
                    let normalizedLW = lW * (pendProbsLB V.! (graphNode toG)) / ( pendProbsUB V.! (graphNode g))
                        normalizedUW = uW * (pendProbsUB V.! (graphNode toG)) / ( pendProbsLB V.! (graphNode g))
                    lT <- encodeTransition [normalizedLW] tolVar
                    uT <- encodeTransition [normalizedUW] touVar
                    return (lT, uT)

              | otherwise = error "there must be at least one edge in the support graph associated with this edge in graph H"
        cases

  in do
    -- a little sanity check
    unless (graphNode g == gnId gn) $ error "Encoding Push encountered a non consistent pair GNode - graphNode"
    --DBG.traceM $ "Encoding a Gnode corresponding to a push semiconf"
    transitions <- mapM pushEnc fNodes
    lvar <- liftIO $ fromJust <$> HT.lookup lTypVarMap (gId g)
    uvar <- liftIO $ fromJust <$> HT.lookup uTypVarMap (gId g)
    lEq <- mkGe lvar =<< mkAdd (map fst transitions)
    uEq <- mkLe uvar =<< mkAdd (map snd transitions)
    -- debugging
    eqString <- astToString lEq
    DBG.traceM $ "Asserting Push/Support equation (lower bound): " ++ eqString
    eqString <- astToString uEq
    DBG.traceM $ "Asserting Push/Support equation (upper bound): " ++ eqString
    -- it's greater than zero for sure!
    lgtZero <- mkGt lvar =<< mkRational (0 :: Prob)
    ugtZero <- mkGt uvar =<< mkRational (0 :: Prob)
    lleqOne <- mkLe lvar =<< mkRational (1 :: Prob)
    uleqOne <- mkLe uvar =<< mkRational (1 :: Prob)
    soundness <- mkLe lvar uvar
    return ([lEq, lgtZero, lleqOne, uEq, ugtZero, uleqOne, soundness])


encodeShift :: (TypicalVarMap, TypicalVarMap)
  -> Vector GNode
  -> (GNode -> Bool)
  -> GNode
  -> GraphNode pstate
  -> Vector Prob
  -> Vector Prob
  -> Z3 ([AST])
encodeShift (lTypVarMap, uTypVarMap) gGraph isInH g gn pendProbsLB pendProbsUB =
  let fNodes = IntSet.toList . IntSet.filter (\idx -> isInH (gGraph V.! idx)) . Map.keysSet $ edges g
      shiftEnc toIdx = do
        tolVar <- liftIO $ fromJust <$> HT.lookup lTypVarMap toIdx
        touVar <- liftIO $ fromJust <$> HT.lookup uTypVarMap toIdx
        -- a small trick to be refactored later
        let toG = gGraph V.! toIdx
            p = prob . fromJust . Set.lookupLE (Edge (graphNode toG) 0) $ internalEdges gn
            normalizedLP = p * (pendProbsLB V.! (graphNode toG)) / ( pendProbsUB V.! (graphNode g))
            normalizedUP = p * (pendProbsUB V.! (graphNode toG)) / ( pendProbsLB V.! (graphNode g))
        lT<- encodeTransition [normalizedLP] tolVar
        uT <- encodeTransition [normalizedUP] touVar
        return (lT, uT)

  in do
  -- a little sanity check
  unless (graphNode g == gnId gn) $ error "Encoding Shift encountered a non consistent pair GNode - graphNode"
  --DBG.traceM $ "Encoding a Gnode corresponding to a shift semiconf"
  transitions <- mapM shiftEnc fNodes
  lvar <- liftIO $ fromJust <$> HT.lookup lTypVarMap (gId g)
  uvar <- liftIO $ fromJust <$> HT.lookup uTypVarMap (gId g)
  lEq <- mkGe lvar =<< mkAdd (map fst transitions)
  uEq <- mkLe uvar =<< mkAdd (map snd transitions)
  -- debugging
  eqString <- astToString lEq
  DBG.traceM $ "Asserting Shift equation (lower bound): " ++ eqString
  eqString <- astToString uEq
  DBG.traceM $ "Asserting Shift equation (upper bound): " ++ eqString
  -- it's greater than zero for sure!
  lgtZero <- mkGt lvar =<< mkRational (0 :: Prob)
  ugtZero <- mkGt uvar =<< mkRational (0 :: Prob)
  lleqOne <- mkLe lvar =<< mkRational (1 :: Prob)
  uleqOne <- mkLe uvar =<< mkRational (1 :: Prob)
  soundness <- mkLe lvar uvar
  return ([lEq, lgtZero, lleqOne, uEq, ugtZero, uleqOne, soundness])






{-# LANGUAGE DeriveGeneric #-}
{- |
   Module      : Pomc.Prob.GGraph
   Copyright   : 2023 Francesco Pontiggia
   License     : MIT
   Maintainer  : Francesco Pontiggia
-}

module Pomc.Prob.GGraph (GGraph
                        , GNode(..)
                        , qualitativeModelCheck
                        ) where

import Pomc.Prob.ProbUtils
import Pomc.State(State(..), Input)
import Pomc.SatUtil(SatState(..))
import Pomc.Prec (Prec(..))
import Pomc.Potl(Formula(..))
import Pomc.PropConv(APType)

import Pomc.GStack(GStack)
import qualified Pomc.GStack as GS

import qualified Pomc.CustoMap as CM

import qualified Pomc.Prob.GReach as GR
import Pomc.Prob.GReach(GRobals)

import Pomc.Prob.SupportGraph(GraphNode(..), Edge(..), SupportGraph)

import Pomc.Prob.ProbEncoding(ProbEncodedSet)
import qualified Pomc.Prob.ProbEncoding as PE

import qualified Pomc.Encoding as E

import Data.IntMap.Strict(IntMap)
import qualified Data.IntMap.Strict as Map

import Data.Set(Set)
import qualified Data.Set as Set

import Data.IntSet(IntSet)
import qualified Data.IntSet as IntSet

import Control.Monad(when, unless, forM_, foldM, forM)
import Control.Monad.ST (ST)

import Data.STRef (STRef, newSTRef, readSTRef, modifySTRef')
import Data.Maybe (fromJust, isNothing, mapMaybe)

import GHC.Generics (Generic)
import Data.Hashable
import qualified Data.HashTable.ST.Basic as BH

import qualified Data.Vector.Mutable as MV
import Data.Vector(Vector)
import qualified Data.Vector as V

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
  getStateProps b (AugState _ _ p) = getStateProps b p
  {-# INLINABLE getStateProps #-}

-- the global variables in the algorithm
data GGlobals s pstate = GGlobals
  { idSeq      :: STRef s Int
  , ggraphMap   :: HashTable s (Int, State) Int
  , gGraph      :: STRef s (CM.CustoMap s GNode)
  , grGlobals   :: GRobals s (AugState pstate)
  }


-- the G Graph computed by this function
type GGraph s = CM.CustoMap s GNode

-- requires: the initial semiconfiguration has id 0
-- requires: idSeq is at 0
-- pstate: a parametric type for states of the input popa
decomposeGGraph :: (Ord pstate, Hashable pstate, Show pstate)
                => GGlobals s pstate
                -> DeltaWrapper pstate
                -> [State] -- initial states of the phiOpa 
                -> (Int -> ST s (GraphNode pstate)) -- getter for retrieving a graphNode associated with the given int
                -> (Int -> Bool) -- is a semiconf pending?
                -> ST s (GGraph s, Int)
decomposeGGraph gglobals delta phiInitials getGn isPending = do
  iniGn <- getGn 0
  let iniLabel = getLabel . fst . semiconf $ iniGn
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
  initialNodes <- readSTRef . idSeq $ gglobals
  forM_ filtered $ \s -> decompose gglobals delta getGn isPending (iniGn, s)
  idx <- readSTRef . idSeq $ gglobals
  g <- CM.take idx <$> readSTRef (gGraph gglobals)
  return (g, initialNodes)

decompose :: (Ord pstate, Hashable pstate, Show pstate)
          => GGlobals s pstate -- global variables of the algorithm
          -> DeltaWrapper pstate
          -> (Int -> ST s (GraphNode pstate)) -- getter for retrieving a graphNode associated with the given int
          -> (Int -> Bool) -- is a semiconf pending?
          -> (GraphNode pstate, State) -- current GNode
          -> ST s ()
decompose gglobals delta getGn isPending (gn, p) = do
  let
    (q,g) = semiconf gn
    precRel = (prec delta) (fst . fromJust $ g) (getLabel q)
    cases
      -- a sanity check
      | getLabel q /= E.extractInput (bitenc delta) (current p) = error "inconsistent GNode when decomposing the G Graph"

      -- this case includes the initial push
      | (isNothing g) || precRel == Just Yield =
        decomposePush gglobals delta getGn isPending (gn,p)

      | precRel == Just Equal =
        decomposeShift gglobals delta getGn isPending (gn, p)

      | precRel == Just Take = error $ "a pop transition cannot be reached in the augmented graph of pending semiconfs" ++ show gn
      | otherwise = return ()
  cases


decomposePush :: (Ord pstate, Hashable pstate, Show pstate)
              => GGlobals s pstate -- global variables of the algorithm
              -> DeltaWrapper pstate
              -> (Int -> ST s (GraphNode pstate)) -- getter for retrieving a graphNode associated with the given int
              -> (Int -> Bool) -- is a semiconf pending?
              -> (GraphNode pstate, State) -- current gnode
              -> ST s ()
decomposePush gglobals delta getGn isPending (gn, p) =
  let fPendingPushSemiconfs = Set.toList . Set.filter isPending . Set.map to $ internalEdges gn
      fPendingSuppSemiconfs = Set.toList . Set.filter isPending . Set.map to $ supportEdges gn
      fPushPhiStates = (phiDeltaPush delta) p
  in do
    -- handling the push edges
    fPushGns <- mapM getGn fPendingPushSemiconfs
    let fPushGnodes = [(gn1, p1) | gn1 <- fPushGns, p1 <- fPushPhiStates, (getLabel . fst . semiconf $ gn1) == E.extractInput (bitenc delta) (current p1)]
    forM_ fPushGnodes $ \(gn1, p1) -> decomposeEdge gglobals delta getGn isPending (gn, p) (PE.empty . proBitenc $ delta) (gn1, p1)
    -- handling the support edges
    fSuppGns <- mapM getGn fPendingSuppSemiconfs
    let leftContext = AugState (getState . fst . semiconf $ gn) (E.extractInput (bitenc delta) (current p)) p
        cDeltaPush (AugState q0 _ p0)  =  [ AugState q1 lab p1 |
                                            (q1, lab, _) <- (deltaPush delta) q0
                                          , p1 <- (phiDeltaPush delta) p0
                                          ]
        cDeltaShift (AugState q0 _ p0) =  [ AugState q1 lab p1 |
                                            (q1, lab, _) <- (deltaShift delta) q0
                                          , p1 <- (phiDeltaShift delta) p0
                                          ]
        cDeltaPop (AugState q0 _ p0) (AugState q1 _ p1)  = [ AugState q2 lab p2 |
                                                             (q2, lab, _) <- (deltaPop delta) q0 q1
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

    fSuppAugStates <- GR.reachableStates (grGlobals gglobals) cDelta leftContext
    let fSuppGnodes = [(gn1, p1, suppSatSet) |
                        gn1 <- fSuppGns
                      , (AugState q lab p1, suppSatSet) <- fSuppAugStates
                      , (getState . fst . semiconf $ gn1) == q
                      , consistentFilter (AugState q lab p1)
                      ]
    forM_ fSuppGnodes $ \(gn1, p1, suppSatSet) -> decomposeEdge gglobals delta getGn isPending (gn, p) suppSatSet (gn1, p1)

decomposeShift :: (Ord pstate, Hashable pstate, Show pstate)
               => GGlobals s pstate -- global variables of the algorithm
               -> DeltaWrapper pstate
               -> (Int -> ST s (GraphNode pstate)) -- getter for retrieving a graphNode associated with the given int
               -> (Int -> Bool) -- is a semiconf pending?
               -> (GraphNode pstate, State) -- current GNopde
               -> ST s ()
decomposeShift gglobals delta getGn isPending (gn, p) =
  let fPendingSemiconfs = Set.toList . Set.filter isPending . Set.map to $ internalEdges gn
      fPhiStates = (phiDeltaShift delta) p
  in do
    -- just a sanity check
    unless (Set.null . supportEdges $ gn) $ error "a shift semiconf cannot have summaries"
    fGns <- mapM getGn fPendingSemiconfs
    let fGnodes = [(gn1, p1) | gn1 <- fGns, p1 <- fPhiStates, (getLabel . fst . semiconf $ gn1) == E.extractInput (bitenc delta) (current p1)]
    forM_ fGnodes $ \(gn1, p1) -> decomposeEdge gglobals delta getGn isPending (gn, p) (PE.empty . proBitenc $ delta) (gn1, p1)

-- decomposing an edge to a new node
decomposeEdge :: (Ord pstate, Hashable pstate, Show pstate)
                 => GGlobals s pstate -- global variables of the algorithm
                 -> DeltaWrapper pstate
                 -> (Int -> ST s (GraphNode pstate)) -- getter for retrieving a graphNode associated with the given int
                 -> (Int -> Bool) -- is a semiconf pending?
                 -> (GraphNode pstate, State) -- current node
                 -> ProbEncodedSet -- for formulae satisfied in a support
                 -> (GraphNode pstate, State) -- to node
                 -> ST s ()
decomposeEdge gglobals delta getGn isPending (gn, p) suppSatSet (gn1, p1) =
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
    when (isNothing maybeId) $ decompose gglobals delta getGn isPending (gn1, p1)

-------- finding the bottom SCCs of subgraph H -------------
type GraphNodesSCC = IntSet

data HGlobals s pstate = HGlobals
  { graph :: GGraph s
  , supportGraph :: SupportGraph s pstate
  , sStack     :: GStack s HEdge
  , bStack     :: GStack s Int
  , cGabow     :: STRef s Int
  , bottomHSCCs  :: STRef s (IntMap GraphNodesSCC) -- we store only those reachable from a not phi initial state
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
  (g, iniCount) <- decomposeGGraph gGlobals delta phiInitials (MV.unsafeRead suppGraph) (pendVector V.!)
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

-- helpers
addtoPath :: HGlobals s pstate -> GNode -> HEdge -> ST s GNode
addtoPath hglobals node edge  = do
  GS.push (sStack hglobals) edge
  sSize <- GS.size $ sStack hglobals
  MV.unsafeModify (graph hglobals) (\g -> g{iValue = sSize }) (gId node)
  GS.push (bStack hglobals) sSize
  return node{iValue = sSize}

merge :: HGlobals s pstate -> GNode -> ST s ()
merge hGlobals g = do
  -- contract the B stack, that represents the boundaries between SCCs on the current path
  GS.popWhile_ (bStack hGlobals) (\x -> iValue g < x)

deleteDescendants :: HGlobals s pstate -> GraphNodesSCC -> IntSet -> ST s IntSet
deleteDescendants hGlobals sccSemiconfs descendants = do
  modifySTRef' (bottomHSCCs hGlobals) $ Map.filterWithKey (\idx scc -> not (IntSet.member idx descendants) || IntSet.disjoint sccSemiconfs scc)
  (\m -> IntSet.filter (`Map.member` m) descendants) <$> readSTRef (bottomHSCCs hGlobals)

isBottom :: HGlobals s pstate -> IntSet -> (Int -> Bool) -> ST s Bool
isBottom hGlobals suppGraphSCC isPending = do
  gns <- forM (IntSet.toList suppGraphSCC) $ MV.unsafeRead (supportGraph hGlobals)
  let checkInternals = all (\e -> IntSet.member (to e) suppGraphSCC) . Set.filter (isPending . to) . internalEdges
      checkSupports  = all (\e -> IntSet.member (to e) suppGraphSCC) . Set.filter (isPending . to) . supportEdges
  return $ all (\gn -> checkInternals gn && checkSupports gn) gns

isAccepting :: HGlobals s pstate -> DeltaWrapper pstate -> [HEdge] -> ST s Bool
isAccepting hGlobals delta sccEdges = do
  gs <- mapM (MV.unsafeRead (graph hGlobals) . toG) sccEdges
  let maybeSupport (Internal _ ) = Nothing
      maybeSupport (Support _ sss) = Just sss
      acceptanceBitVector = PE.unions $ map (PE.encodeSatState (proBitenc delta) . phiNode) gs ++ mapMaybe maybeSupport sccEdges
  return $ PE.isSatisfying acceptanceBitVector

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

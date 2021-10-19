{- |
   Module      : Pomc.SCCAlgorithm
   Copyright   : 2021 Francesco Pontiggia
   License     : MIT
   Maintainer  : Francesco Pontiggia
-}

module Pomc.SCCAlgorithm ( Graph
                         , newGraph
                         , alreadyDiscovered
                         , alreadyVisited
                         , visitGraphFromKey
                         , initialNodes
                         , summariesSize
                         , toCollapsePhase
                         , toSearchPhase
                         , visitNode
                         , createComponent
                         , insertEdge
                         , discoverSummary
                         , updateSCC
                         ) where

import Pomc.SatUtil
import qualified  Pomc.TripleHashTable as THT
import Pomc.GStack(GStack)
import qualified Pomc.GStack as GS

import Control.Monad (forM_, foldM)
import qualified Control.Monad.ST as ST

import Data.STRef (STRef, newSTRef, readSTRef, writeSTRef, modifySTRef')
import Data.Maybe

import Data.Set (Set)
import qualified Data.Set as Set

import Data.Vector (Vector)

import Data.Hashable

import Control.DeepSeq(NFData(..), deepseq)

data GraphNode state = SCComponent
  { getgnId   :: Int -- immutable
  , iValue    :: Int -- changes at each iteration of the Gabow algorithm
  , nodes     :: Set (StateId state, Stack state)
  , edges     :: Set Int
  , preds     :: Set Int
  } | SingleNode
  { getgnId  :: Int
  , iValue   :: Int
  , node     :: (StateId state, Stack state)
  , edges    :: Set Int
  , preds    :: Set Int
  }

instance (NFData state) => NFData (GraphNode state) where
  rnf (SCComponent i iVal ns es p) = i `deepseq` iVal `deepseq` ns `deepseq` es `deepseq` p `deepseq` ()
  rnf (SingleNode  i iVal n es  p)  = i `deepseq` iVal `deepseq` n  `deepseq` es `deepseq` p `deepseq` ()

instance (Show state) => Show (GraphNode  state) where
  show gn =  show $ getgnId gn

instance Eq (GraphNode state) where
  p == q = getgnId p == getgnId q

instance  Ord (GraphNode state) where
  compare p q = compare (getgnId p) (getgnId q)

instance Hashable (GraphNode state) where
  hashWithSalt _ s = getgnId s

type Key state = (StateId state, Stack state)
type Value state = GraphNode state

data Graph s state = Graph
  { idSeq           :: STRef s Int
  , nodeToGraphNode :: THT.TripleHashTable s (Value state)
  , c               :: STRef s Int -- for the Gabow algorithm
  , bStack          :: GStack s Int -- for the Gabow algorithm
  , sStack          :: GStack s Int -- for the Gabow algorithm
  , initials        :: STRef s (Set (Int, Bool))
  , summaries       :: STRef s (Set (Int, Key state))
  }

newGraph :: (NFData state, SatState state, Eq state, Hashable state, Show state)
         => Vector (Key state)
         -> ST.ST s (Graph s state)
newGraph iniNodes = do
  newIdSequence <- newSTRef (1 :: Int)
  tht           <- THT.empty
  newCSequence  <- newSTRef (-1 :: Int)
  newBS         <- GS.new
  newSS         <- GS.new
  newInitials   <- newSTRef (Set.empty)
  newSummaries  <- newSTRef (Set.empty)
  forM_ (iniNodes) $ \key -> do
    newId <- freshPosId newIdSequence
    THT.insert tht (decode key) newId $ SingleNode {getgnId = newId, iValue = 0, node = key, edges = Set.empty, preds = Set.empty};
    modifySTRef' newInitials (Set.insert (newId,True))
  return $ Graph { idSeq = newIdSequence
                 , nodeToGraphNode = tht
                 , c = newCSequence
                 , bStack = newBS
                 , sStack = newSS
                 , initials = newInitials
                 , summaries = newSummaries
                }

----------------------------------------------------------------------------------------
-- the iValue is used in the Gabow algorithm
setgnIValue ::  Int -> GraphNode state -> GraphNode state
setgnIValue new gn@SCComponent{} = gn{iValue = new}
setgnIValue new gn@SingleNode{}  = gn{iValue = new}

resetgnIValue :: GraphNode state -> GraphNode state
resetgnIValue  = setgnIValue 0

-- unsafe
initialNodes :: (NFData state, SatState state, Eq state, Hashable state, Show state)
             =>  Graph s state
             -> ST.ST s (Set (Key state))
initialNodes graph =
  let gnNode (SingleNode{node = n}) = Set.singleton n
      gnNode (SCComponent{nodes=ns})= ns
  in do
    inSet <- readSTRef $ initials graph
    let inIdents = Set.map fst . Set.filter snd $ inSet
    gnNodesList <- THT.lookupMap (nodeToGraphNode graph) (Set.toList inIdents) gnNode
    return $ Set.unions gnNodesList

-- unsafe
alreadyVisited :: (NFData state, SatState state, Eq state, Hashable state, Show state)
               => Graph s state
               -> Key state
               -> ST.ST s Bool
alreadyVisited graph k = do
  graphNode <- THT.lookup (nodeToGraphNode graph) $ decode k
  return $ (iValue graphNode) /= 0

alreadyDiscovered :: (NFData state, SatState state, Eq state, Hashable state, Show state)
                  => Graph s state
                  -> Key state
                  -> ST.ST s Bool
alreadyDiscovered graph key = do
  ident <- THT.lookupId (nodeToGraphNode graph) $ decode key
  if isJust ident
    then do
      inSet <- readSTRef (initials graph)
      return $ not $ Set.member (fromJust ident, True) inSet
    else do
      newIdent <- freshPosId $ idSeq graph
      let sn = SingleNode{getgnId = newIdent,iValue = 0, node = key, edges = Set.empty, preds = Set.empty}
      THT.insert (nodeToGraphNode graph) (decode key) newIdent sn;
      return False

-- unsafe
visitNode :: (NFData state, SatState state, Eq state, Hashable state, Show state)
          => Graph s state
          -> Key state
          -> ST.ST s ()
visitNode graph key = do
  gn <- THT.lookup (nodeToGraphNode graph) $ decode key
  visitGraphNode graph gn


visitGraphNode :: (NFData state, SatState state, Eq state, Hashable state, Show state)
               => Graph s state
               -> GraphNode state
               -> ST.ST s ()
visitGraphNode graph gn = do
  modifySTRef' (initials graph)
    $ \s -> if Set.member (getgnId gn, True) s
              then Set.insert (getgnId gn, False) . Set.delete (getgnId gn, True) $ s
              else s
  GS.push (sStack graph) (getgnId gn);
  sSize <- GS.size $ sStack graph
  THT.modify (nodeToGraphNode graph) (getgnId gn) $ setgnIValue sSize;
  GS.push (bStack graph) sSize

--unsafe
updateSCC :: (NFData state, SatState state, Eq state, Hashable state, Show state)
          => Graph s state
          -> Key state
          -> ST.ST s ()
updateSCC graph key = do
  gn <- THT.lookup (nodeToGraphNode graph) $ decode key
  updateSCCInt graph (iValue gn)

updateSCCInt :: (NFData state, SatState state, Eq state, Hashable state, Show state)
             => Graph s state
             -> Int
             -> ST.ST s ()
updateSCCInt graph iVal =  do
  topElemB <- GS.peek (bStack graph)
  if (iVal  < 0) || (iVal  >=  topElemB)
    then  return ()
    else do
      _ <- GS.pop (bStack graph);
      updateSCCInt graph iVal


-- unsafe
discoverSummary :: (NFData state, SatState state, Eq state, Hashable state, Show state)
                => Graph s state
                -> Key state
                -> Key state
                -> ST.ST s ()
discoverSummary graph fr t = do
  gnFrom <- THT.lookup (nodeToGraphNode graph) $ decode fr
  modifySTRef' (summaries graph) $ Set.insert (getgnId gnFrom, t)

-- unsafe
insertEdge :: (NFData state, SatState state, Eq state, Hashable state, Show state)
           => Graph s state
           -> Key state
           -> Key state
           -> ST.ST s ()
insertEdge graph fromKey toKey = do
  fr <- THT.lookupId (nodeToGraphNode graph) $ decode fromKey
  t  <- THT.lookupId (nodeToGraphNode graph) $ decode toKey
  let e = fromJust t
      insertEd x@SingleNode{edges = es}  = x{edges = Set.insert e es}
      insertEd x@SCComponent{edges = es} = x{edges = Set.insert e es}
      insertPred x@SingleNode{preds = ps}  = x{preds = Set.insert (fromJust fr) ps}
      insertPred x@SCComponent{preds = ps} = x{preds = Set.insert (fromJust fr) ps}
  THT.modify (nodeToGraphNode graph) (fromJust fr) insertEd
  THT.modify (nodeToGraphNode graph) (fromJust t) insertPred

createComponent :: (NFData state, SatState state, Ord state, Hashable state, Show state)
                => Graph s state
                -> Key state
                -> ([state] -> Bool)
                -> ST.ST s Bool
createComponent graph key areFinal = do
  gn <- THT.lookup (nodeToGraphNode graph) $ decode key
  createComponentGn graph gn areFinal

createComponentGn :: (NFData state, SatState state, Ord state, Hashable state, Show state)
                  => Graph s state
                  -> GraphNode state
                  -> ([state] -> Bool)
                  -> ST.ST s Bool
createComponentGn graph gn areFinal =
  let
    toMerge [ident] = do
      cond <- identCond ident
      if cond
        then merge graph [ident] areFinal
        else do
          newC <- freshNegId (c graph);
          THT.modify (nodeToGraphNode graph) ident $ setgnIValue newC;
          return False;
    toMerge idents = merge graph idents areFinal
    identCond ident = THT.lookupApply (nodeToGraphNode graph) ident $ (Set.member ident) . edges
    stackCond = do
      sSize <- GS.size $ sStack graph
      return $ (iValue gn) > sSize
  in do
    topB <- GS.peek (bStack graph)
    if  (iValue gn) == topB
      then do
        _ <- GS.pop (bStack graph)
        idents <- GS.popUntil (sStack graph) stackCond
        toMerge idents
      else return False

merge :: (NFData state, SatState state, Ord state, Hashable state, Show state)
      => Graph s state
      -> [Int]
      -> ([state] -> Bool)
      -> ST.ST s Bool
merge graph idents areFinal =
  let
    gnNode SingleNode{node = n}    = Set.singleton n
    gnNode SCComponent{nodes = ns} = ns
    identsSet = Set.fromList idents
    newId = head idents
  in do
    newC <- freshNegId (c graph)
    gnsNodes <- THT.lookupMap (nodeToGraphNode graph) idents gnNode
    gnsEdges <- THT.lookupMap (nodeToGraphNode graph) idents $ (Set.filter $ \e -> not $ Set.member e identsSet) . edges
    gnsPreds <- THT.lookupMap (nodeToGraphNode graph) idents $ (Set.filter $ \p -> not $ Set.member p identsSet) . preds
    let gnsNodesSet = Set.unions gnsNodes
        gnsEdgesSet = Set.unions gnsEdges
        gnsPredsSet = Set.unions gnsPreds
        newgn = SCComponent{nodes = gnsNodesSet, getgnId = newId, iValue = newC, edges = gnsEdgesSet, preds = gnsPredsSet}
        sub n = if Set.member n identsSet
                  then newId
                  else n
        updateGn x@SingleNode{edges = es}  = x{edges = Set.map sub es}
        updateGn x@SCComponent{edges = es} = x{edges = Set.map sub es}
        gnStates = Set.map (getState . fst) gnsNodesSet
    THT.fuse (nodeToGraphNode graph) (Set.map decode gnsNodesSet) newId newgn;
    THT.multModify (nodeToGraphNode graph) (Set.toList gnsPredsSet) updateGn;
    modifySTRef' (summaries graph) $ Set.map $ \(f,t) -> (sub f,t);
    modifySTRef' (initials graph)  $ Set.map $ \(n,b) -> (sub n,b);
    return $ areFinal . Set.toList $ gnStates

summariesSize :: (NFData state, SatState state, Eq state, Hashable state, Show state) => Graph s state -> ST.ST s Int
summariesSize graph = do
  summ <- readSTRef $ summaries graph
  return $ Set.size summ

toCollapsePhase :: (NFData state, SatState state, Eq state, Hashable state, Show state) => Graph s state -> ST.ST s (Set (Int,Bool))
toCollapsePhase graph =
  let resolveSummary (fr, key) = do
        alrDir <- alreadyDiscovered graph key
        ident <- THT.lookupId (nodeToGraphNode graph) $ decode key
        let summ = fromJust ident
            insertEd x@SingleNode{edges = es}  = x{edges = Set.insert summ es}
            insertEd x@SCComponent{edges = es} = x{edges = Set.insert summ es}
        THT.modify (nodeToGraphNode graph) fr insertEd
        return (fromJust ident, not $ alrDir)
  in do
    THT.modifyAll (nodeToGraphNode graph) resetgnIValue
    summ <- readSTRef $ summaries graph
    newInitials <- mapM resolveSummary $ Set.toList summ
    modifySTRef' (initials graph) $ Set.map $ \(ident, _) -> (ident,True)
    return $ Set.fromList newInitials

toSearchPhase :: (NFData state, SatState state, Eq state, Hashable state, Show state) => Graph s state -> (Set (Int,Bool)) -> ST.ST s ()
toSearchPhase graph newInitials = do
  THT.modifyAll (nodeToGraphNode graph) resetgnIValue
  writeSTRef (initials graph) newInitials;
  writeSTRef (summaries graph) Set.empty

--unsafe
visitGraphFromKey :: (NFData state, SatState state, Ord state, Hashable state, Show state)
                  => Graph s state
                  -> ([state] -> Bool)
                  -> Key state
                  ->  ST.ST s Bool
visitGraphFromKey graph areFinal key = do
  gn <- THT.lookup (nodeToGraphNode graph) $ decode key
  visitGraphFrom graph areFinal gn

-- unsafe
visitGraphFrom :: (NFData state, SatState state, Ord state, Hashable state, Show state)
               => Graph s state
               -> ([state] -> Bool)
               -> GraphNode state
               -> ST.ST s Bool
visitGraphFrom graph areFinal gn = do
  visitGraphNode graph gn;
  success <-  foldM (\acc nextEdge -> if acc
                                        then return True
                                        else do
                                          nextGn <- THT.lookupApply (nodeToGraphNode graph) nextEdge id
                                          if (iValue nextGn) == 0
                                            then visitGraphFrom graph areFinal nextGn
                                            else  do
                                              updateSCCInt graph (iValue nextGn)
                                              return False)
                    False
                    (edges gn)
  if success
    then return True
    else createComponentGn graph gn areFinal

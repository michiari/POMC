{- |
   Module      : Pomc.SCCAlgorithm
   Copyright   : 2021 Francesco Pontiggia
   License     : MIT
   Maintainer  : Francesco Pontiggia
-}

module Pomc.SCCAlgorithm ( Graph
                         , SummaryBody
                         , Edge
                         , newGraph
                         , alreadyDiscovered
                         , alreadyVisited
                         , visitGraphFromKey
                         , initialNodes
                         , nullSummaries
                         , toCollapsePhase
                         , toSearchPhase
                         , visitNode
                         , createComponent
                         , discoverSummaryBody
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

import Data.List(partition)

import Data.Vector (Vector)

import Data.Hashable

import Control.DeepSeq(NFData(..))

type SummaryBody = Set Int
  
data Edge = Internal -- a transition
  { to  :: Int 
  } | Summary -- a chain support
  { to :: Int
  , body :: Set Int
  } deriving (Show, Eq, Ord)


data GraphNode state = SCComponent
  { gnId     :: Int
  , iValue   :: Int -- changes at each iteration of the Gabow algorithm
  , nodes    :: [(StateId state, Stack state)]
  , edges    :: [Edge]
  , seIdents :: Set Int -- nodes of the self edges
  } | SingleNode
  { gnId   :: Int
  , iValue :: Int
  , node   :: (StateId state, Stack state)
  , edges  :: [Edge]
  }

instance (Show state) => Show (GraphNode  state) where
  show gn =  show $  gnId gn

instance Eq (GraphNode state) where
  p == q =  gnId p ==  gnId q

instance  Ord (GraphNode state) where
  compare p q = compare ( gnId p) ( gnId q)

instance Hashable (GraphNode state) where
  hashWithSalt salt s = hashWithSalt salt $  gnId s

type Key state = (StateId state, Stack state)
type Value state = GraphNode state

data Graph s state = Graph
  { idSeq      :: STRef s Int
  , gnMap      :: THT.TripleHashTable s (Value state)
  , bStack     :: GStack s Int 
  , sStack     :: GStack s (Maybe Edge) 
  , initials   :: STRef s (Set (Int, Bool))
  , summaries  :: STRef s [(Int, SummaryBody, Key state)]
  }

newGraph :: (NFData state, SatState state, Eq state, Hashable state, Show state)
         => Vector (Key state)
         -> ST.ST s (Graph s state)
newGraph iniNodes = do
  newIdSequence <- newSTRef (1 :: Int)
  tht           <- THT.empty
  newBS         <- GS.new
  newSS         <- GS.new
  newInitials   <- newSTRef (Set.empty)
  newSummaries  <- newSTRef []
  forM_ (iniNodes) $ \key -> do
    newId <- freshPosId newIdSequence
    THT.insert tht (decode key) newId $ SingleNode { gnId = newId, iValue = 0, node = key, edges = []} 
    modifySTRef' newInitials (Set.insert (newId,True))
  return $ Graph { idSeq = newIdSequence
                 , gnMap = tht
                 , bStack = newBS
                 , sStack = newSS
                 , initials = newInitials
                 , summaries = newSummaries
                }

setgnIValue ::  Int -> GraphNode state -> GraphNode state
setgnIValue new gn@SCComponent{} = gn{iValue = new}
setgnIValue new gn@SingleNode{}  = gn{iValue = new}

resetgnIValue :: GraphNode state -> GraphNode state
resetgnIValue  = setgnIValue 0

sEdgeIdents :: GraphNode state -> Set Int
sEdgeIdents SingleNode{} = Set.empty 
sEdgeIdents SCComponent{seIdents = seIx} = seIx


summaryIdents :: Edge -> Set Int
summaryIdents (Internal _) = Set.empty 
summaryIdents (Summary _ b)  = b

visitedIdents :: Edge -> Set Int 
visitedIdents (Internal t) = Set.singleton t 
visitedIdents (Summary t b) = Set.insert t b

gnNode :: GraphNode state -> [(StateId state, Stack state)]
gnNode SingleNode{node = n}    = [n]
gnNode SCComponent{nodes = ns} = ns

initialNodes :: (NFData state, SatState state, Eq state, Hashable state, Show state)
             =>  Graph s state
             -> ST.ST s [(Key state)]
initialNodes graph = do
  inSet <- readSTRef $ initials graph
  let inIdents = Set.map fst . Set.filter snd $ inSet
  gnNodesList <- THT.lookupMap (gnMap graph) (Set.toList inIdents) gnNode
  return $ concat gnNodesList

-- unsafe
alreadyVisited :: (NFData state, SatState state, Eq state, Hashable state, Show state)
               => Graph s state
               -> Key state
               -> ST.ST s Bool
alreadyVisited graph key = do
  gn <- THT.lookup (gnMap graph) $ decode key
  return $ (iValue gn) /= 0

alreadyDiscovered :: (NFData state, SatState state, Eq state, Hashable state, Show state)
                  => Graph s state
                  -> Key state
                  -> ST.ST s Bool
alreadyDiscovered graph key = do
  ident <- THT.lookupId (gnMap graph) $ decode key
  case ident of 
    Just i -> do
      inSet <- readSTRef (initials graph)
      return $ not $ Set.member (i, True) inSet
    Nothing -> do 
      newIdent <- freshPosId $ idSeq graph
      let sn = SingleNode{ gnId = newIdent,iValue = 0, node = key, edges = []}
      THT.insert (gnMap graph) (decode key) newIdent sn
      return False

visitNode :: (NFData state, SatState state, Eq state, Hashable state, Show state)
          => Graph s state
          -> Maybe Edge
          -> Key state
          -> ST.ST s ()
visitNode graph me key = do
  gn <- THT.lookup (gnMap graph) $ decode key
  visitGraphNode graph me gn


visitGraphNode :: (NFData state, SatState state, Eq state, Hashable state, Show state)
               => Graph s state
               -> Maybe Edge
               -> GraphNode state
               -> ST.ST s ()
visitGraphNode graph me gn = do
  modifySTRef' (initials graph)
    $ \s -> if Set.member ( gnId gn, True) s
              then Set.insert ( gnId gn, False) . Set.delete ( gnId gn, True) $ s
              else s
  GS.push (sStack graph) me
  sSize <- GS.size $ sStack graph
  THT.modify (gnMap graph) ( gnId gn) $ setgnIValue sSize
  GS.push (bStack graph) sSize

--unsafe
updateSCC :: (NFData state, SatState state, Eq state, Hashable state, Show state)
          => Graph s state
          -> Key state
          -> ST.ST s ()
updateSCC graph key = do
  gn <- THT.lookup (gnMap graph) $ decode key
  updateSCCInt graph (iValue gn)

updateSCCInt :: (NFData state, SatState state, Eq state, Hashable state, Show state)
             => Graph s state
             -> Int
             -> ST.ST s ()
updateSCCInt graph iVal
  | iVal < 0 =  return () 
  | otherwise = GS.popWhile_ (bStack graph) (\x -> iVal < x)

discoverSummaryBody :: (NFData state, SatState state, Eq state, Hashable state, Show state) 
                        => Graph s state 
                        -> StateId state 
                        -> ST.ST s SummaryBody
discoverSummaryBody graph fr  = do  
  let 
      containsSId SingleNode{node = n} = fst n == fr 
      containsSId SCComponent{nodes=ns} = elem fr . map fst $ ns
      cond Nothing = return False 
      cond (Just e) = THT.lookupApply (gnMap graph) (to e) $ not . containsSId 
  b <- GS.peekWhileM (sStack graph) cond
  return $ Set.unions . map (visitedIdents . fromJust) $ b

discoverSummary :: (NFData state, SatState state, Eq state, Hashable state, Show state)
                => Graph s state
                -> Key state
                -> SummaryBody
                -> Key state
                -> ST.ST s ()
discoverSummary graph fr b t = do
  gnFrom <- THT.lookup (gnMap graph) $ decode fr
  modifySTRef' (summaries graph) $ \l -> ( gnId gnFrom, b, t):l


insertEd :: Bool -> Edge -> GraphNode state -> GraphNode state 
insertEd False e x@SingleNode{edges = es}     = x{edges = e : es}
insertEd False e x@SCComponent{edges = es}    = x{edges = e : es}
insertEd True  e x@SCComponent{seIdents = is}  = x{seIdents = Set.union is $ summaryIdents e}
insertEd True  e SingleNode{gnId = g, iValue = i, node = n, edges = es}   = 
  SCComponent{gnId = g, iValue = i, nodes = [n], edges = es, seIdents = summaryIdents e}

-- unsafe
insertEdge :: (NFData state, SatState state, Eq state, Hashable state, Show state) 
                  => Graph s state 
                  -> Key state 
                  -> Key state
                  -> Maybe SummaryBody
                  -> ST.ST s Edge
insertEdge graph fromKey toKey  sb = do 
  mfr <- THT.lookupId (gnMap graph) $ decode fromKey
  mto  <- THT.lookupId (gnMap graph) $ decode toKey
  let t = fromJust mto
      fr = fromJust mfr
      ins Nothing = Internal t
      ins (Just b) = Summary {to = t, body = b}
      e = ins sb
      self = t == fr 
  THT.modify (gnMap graph) fr $ insertEd self e
  return e

createComponent :: (NFData state, SatState state, Ord state, Hashable state, Show state)
                => Graph s state
                -> Key state
                -> ([state] -> Bool)
                -> ST.ST s Bool
createComponent graph key areFinal = do
  gn <- THT.lookup (gnMap graph) $ decode key
  createComponentGn graph gn areFinal

createComponentGn :: (NFData state, SatState state, Ord state, Hashable state, Show state)
                  => Graph s state
                  -> GraphNode state
                  -> ([state] -> Bool)
                  -> ST.ST s Bool
createComponentGn graph gn areFinal =
  let
    toMerge [_] = uniMerge graph (gnId gn) areFinal
    toMerge (Nothing : idents) = merge graph (gnId gn : (map (to . fromJust) idents)) areFinal 
    toMerge idents = merge graph (map (to . fromJust) idents) areFinal 
  in do
    topB <- GS.peek $ bStack graph
    sSize <- GS.size $ sStack graph
    if  (iValue gn) == topB
      then do
        GS.pop_ (bStack graph)
        idents <- GS.multPop (sStack graph) (sSize - (iValue gn) + 1)
        toMerge idents
      else return False 

uniMerge :: (NFData state, SatState state, Ord state, Hashable state, Show state)
      => Graph s state
      -> Int
      -> ([state] -> Bool)
      -> ST.ST s Bool
uniMerge graph ident areFinal = do
    THT.modify (gnMap graph) ident $ setgnIValue (-1)
    gn <- THT.lookupApply (gnMap graph) ident id 
    let cases SCComponent{seIdents = se} = do 
              summgnNodes <- THT.lookupMap (gnMap graph) (Set.toList se) gnNode
              let summStates = map (getState . fst) . concat $ summgnNodes
                  gnStates = map (getState . fst) . nodes $ gn
              return $ areFinal (summStates ++ gnStates)
        cases _ = return False
    cases gn

merge :: (NFData state, SatState state, Ord state, Hashable state, Show state)
      => Graph s state
      -> [Int]
      -> ([state] -> Bool)
      -> ST.ST s Bool
merge graph idents areFinal = do
  gns <- THT.lookupMap(gnMap graph) idents id 
  let newId = head idents
      identsSet = Set.fromList idents
      gnsNodes = concat . map gnNode $ gns
      filterEd es = partition (\e -> Set.member (to e) identsSet) es
      (selfEdges, gnsEdgesSet) = unzip . map (filterEd . edges) $ gns
      setSummaryIdents s = Set.unions . map summaryIdents $ s
      subgnsSEIdentsSet = Set.unions . map setSummaryIdents $ selfEdges
      gnsSEIdentsSet = Set.unions . map sEdgeIdents $ gns
      allSeIdentsSet = Set.union subgnsSEIdentsSet gnsSEIdentsSet
      allEdges = concat gnsEdgesSet
      newgn = SCComponent{nodes = gnsNodes,  gnId = newId, iValue = (-1), edges = allEdges, seIdents = allSeIdentsSet}
  THT.merge (gnMap graph) (map decode gnsNodes) newId newgn
  summgnNodes <- THT.lookupMap (gnMap graph) (Set.toList allSeIdentsSet) gnNode
  let summStates = map (getState . fst) . concat $ summgnNodes
      gnStates = map (getState . fst) gnsNodes
  return $ areFinal $ gnStates ++ summStates

nullSummaries :: (NFData state, SatState state, Eq state, Hashable state, Show state) 
              => Graph s state 
              -> ST.ST s Bool
nullSummaries graph = do
  summ <- readSTRef $ summaries graph
  return $ null summ

toCollapsePhase :: (NFData state, SatState state, Eq state, Hashable state, Show state) 
                => Graph s state 
                -> ST.ST s (Set (Int,Bool))
toCollapsePhase graph =
  let resolveSummary (fr, sb, key) = do
        alrDir <- alreadyDiscovered graph key
        mto <- THT.lookupId (gnMap graph) $ decode key
        let t = fromJust mto
            e = Summary t sb
            self = t == fr 
        THT.modify (gnMap graph) fr $ insertEd self e 
        return (t, not $ alrDir)
  in do
    THT.modifyAll (gnMap graph) resetgnIValue
    summ <- readSTRef $ summaries graph
    newInitials <- mapM resolveSummary summ
    modifySTRef' (initials graph) $ Set.map $ \(i, _) -> (i,True)
    return $ Set.fromList newInitials

toSearchPhase :: (NFData state, SatState state, Eq state, Hashable state, Show state) 
              => Graph s state 
              -> Set (Int,Bool) 
              -> ST.ST s ()
toSearchPhase graph newInitials = do
  THT.modifyAll (gnMap graph) resetgnIValue
  writeSTRef (initials graph) newInitials 
  writeSTRef (summaries graph) []

visitGraphFromKey :: (NFData state, SatState state, Ord state, Hashable state, Show state)
                  => Graph s state
                  -> ([state] -> Bool)
                  -> Maybe Edge
                  -> Key state
                  ->  ST.ST s Bool
visitGraphFromKey graph areFinal e key = do
  gn <- THT.lookup (gnMap graph) $ decode key
  visitGraphFrom graph areFinal e gn

-- unsafe
visitGraphFrom :: (NFData state, SatState state, Ord state, Hashable state, Show state)
               => Graph s state
               -> ([state] -> Bool)
               -> Maybe Edge
               -> GraphNode state
               -> ST.ST s Bool
visitGraphFrom graph areFinal e gn = do
  visitGraphNode graph e gn 
  success <-  foldM (\acc ne -> if acc
                                  then return True
                                  else do
                                    nextGn <- THT.lookupApply (gnMap graph) (to ne) id
                                    if (iValue nextGn) == 0
                                      then visitGraphFrom graph areFinal (Just ne) nextGn
                                      else  do
                                        updateSCCInt graph (iValue nextGn)
                                        return False)
                    False
                    (edges gn)
  if success
    then return True
    else createComponentGn graph gn areFinal

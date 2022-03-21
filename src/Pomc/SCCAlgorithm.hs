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

import Data.Vector (Vector)

import Data.Hashable

import Control.DeepSeq(NFData(..), deepseq)

type SummaryBody = [Edge]
  
data Edge = Internal -- a transition
  { to  :: Int 
  } | Summary -- a chain support
  { to :: Int
  , body :: [Edge]
  } deriving (Show, Eq, Ord)

data GraphNode state = SCComponent
  { gnId   :: Int
  , iValue :: Int -- changes at each iteration of the Gabow algorithm
  , nodes  :: Set (StateId state, Stack state)
  , edges  :: Set Edge
  } | SingleNode
  { gnId   :: Int
  , iValue :: Int
  , node   :: (StateId state, Stack state)
  , edges  :: Set Edge
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
    THT.insert tht (decode key) newId $ SingleNode { gnId = newId, iValue = 0, node = key, edges = Set.empty} 
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

summaryIdents :: Edge -> Int -> Set Int
summaryIdents (Internal _)  _ = Set.empty 
summaryIdents (Summary t b) i 
  | t /=  i = Set.empty 
  | otherwise = Set.unions . map sNodes $ b 
    where sNodes (Internal t) = Set.singleton t
          sNodes (Summary t' b') = Set.insert t' . Set.unions . map sNodes $ b'

gnNode :: GraphNode state -> Set (StateId state, Stack state)
gnNode SingleNode{node = n}    = Set.singleton n
gnNode SCComponent{nodes = ns} = ns

initialNodes :: (NFData state, SatState state, Eq state, Hashable state, Show state)
             =>  Graph s state
             -> ST.ST s (Set (Key state))
initialNodes graph = do
  inSet <- readSTRef $ initials graph
  let inIdents = Set.map fst . Set.filter snd $ inSet
  gnNodesList <- THT.lookupMap (gnMap graph) (Set.toList inIdents) gnNode
  return $ Set.unions gnNodesList

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
      let sn = SingleNode{ gnId = newIdent,iValue = 0, node = key, edges = Set.empty}
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


-- unsafe
discoverSummaryBody :: (NFData state, SatState state, Eq state, Hashable state, Show state) 
                        => Graph s state 
                        -> StateId state 
                        -> ST.ST s SummaryBody
discoverSummaryBody graph fr  = do  
  let 
      containsSId SingleNode{node = n} = fst n == fr 
      containsSId SCComponent{nodes=ns} = Set.member fr . Set.map fst $ ns
      cond Nothing = return False 
      cond (Just e) = THT.lookupApply (gnMap graph) (to e) $ not . containsSId 
  b <- GS.peekWhileM (sStack graph) cond
  return $ map fromJust b

discoverSummary :: (NFData state, SatState state, Eq state, Hashable state, Show state)
                => Graph s state
                -> Key state
                -> SummaryBody
                -> Key state
                -> ST.ST s ()
discoverSummary graph fr b t = do
  gnFrom <- THT.lookup (gnMap graph) $ decode fr
  modifySTRef' (summaries graph) $ \l -> ( gnId gnFrom, b, t):l

-- unsafe
insertEdge :: (NFData state, SatState state, Eq state, Hashable state, Show state) 
                  => Graph s state 
                  -> Key state 
                  -> Key state
                  -> Maybe SummaryBody
                  -> ST.ST s Edge
insertEdge graph fromKey toKey  ms = do 
  fr <- THT.lookupId (gnMap graph) $ decode fromKey
  t  <- THT.lookupId (gnMap graph) $ decode toKey
  let e = fromJust t
      efr = fromJust fr
      ins Nothing = Internal e
      ins (Just b) = Summary {to = e, body = b}
      insertEd x@SingleNode{edges = es}  = x{edges = Set.insert (ins ms) es}
      insertEd x@SCComponent{edges = es} = x{edges = Set.insert (ins ms) es}
  THT.modify (gnMap graph) efr insertEd
  return $ ins ms

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
    toMerge [ident] = uniMerge graph (gnId gn) areFinal
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
    (gnStates, identCond) <- THT.lookupApply (gnMap graph) ident $ 
      \gn  -> (Set.map (getState . fst) . gnNode $ gn, (Set.member ident) . Set.map to . edges $ gn)
    summIdents <- THT.lookupApply (gnMap graph) ident $
      Set.map (\e -> summaryIdents e ident) . edges
    summgnNodesSet <- THT.lookupMap (gnMap graph) (Set.toList . Set.unions $ summIdents) gnNode
    let summStates = Set.toList . Set.map (getState . fst) . Set.unions $ summgnNodesSet
    THT.modify (gnMap graph) ident $ setgnIValue (-1)
    return $ identCond && (areFinal $ summStates ++ (Set.toList gnStates)) 

merge :: (NFData state, SatState state, Ord state, Hashable state, Show state)
      => Graph s state
      -> [Int]
      -> ([state] -> Bool)
      -> ST.ST s Bool
merge graph idents areFinal = do
  gns <- THT.lookupMap(gnMap graph) idents id 
  let newId = head idents
      identsSet = Set.fromList idents
      gnsNodesSet = Set.unions . map gnNode $ gns
      gnsEdgesSet = Set.unions . map edges  $ gns
      newgn = SCComponent{nodes = gnsNodesSet,  gnId = newId, iValue = (-1), edges = gnsEdgesSet}
      gnStates = Set.toList $ Set.map (getState . fst) gnsNodesSet
      summIdents = Set.map (\e -> summaryIdents e newId) $ gnsEdgesSet 
  THT.merge (gnMap graph) (Set.map decode gnsNodesSet) newId newgn
  summgnNodesSet <- THT.lookupMap (gnMap graph) (Set.toList . Set.unions $ summIdents) gnNode
  let summStates = Set.toList . Set.map (getState . fst) . Set.unions $ summgnNodesSet
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
        t <- THT.lookupId (gnMap graph) $ decode key
        let e = fromJust t
            s = Summary e sb
            insertEd x@SingleNode{edges = es}  = x{edges = Set.insert s es}
            insertEd x@SCComponent{edges = es} = x{edges = Set.insert s es}
        THT.modify (gnMap graph) fr insertEd
        return (e, not $ alrDir)
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

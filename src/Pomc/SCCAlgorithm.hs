{- |
   Module      : Pomc.SCCAlgorithm
   Copyright   : 2021-2023 Francesco Pontiggia
   License     : MIT
   Maintainer  : Francesco Pontiggia
-}

module Pomc.SCCAlgorithm ( Graph
                         , Command(..)
                         , newGraph
                         , initialNodes
                         , updateSccInitialWith
                         , updateSCCs
                         , createComponentGn
                         , insertSummary
                         , toSearchPhase
                         , toCollapsePhase
                         , updateSccInitial
                         ) where

import Pomc.SatUtil

import Pomc.GStack(GStack)
import qualified Pomc.GStack as GS

import Pomc.OmegaEncoding(OmegaBitencoding, OmegaEncodedSet)
import qualified Pomc.OmegaEncoding as OE

import Pomc.CustoMap(CustoMap)
import qualified Pomc.CustoMap as CM

import Control.Monad (forM, forM_, when, unless, foldM)
import qualified Control.Monad.ST as ST
import Data.STRef (STRef, newSTRef, readSTRef, writeSTRef, modifySTRef')

import qualified Data.HashTable.ST.Basic as BH

import Data.IntMap.Strict(IntMap)
import qualified Data.IntMap.Strict as Map

import Data.Vector (Vector)
import Data.Maybe (catMaybes, fromJust, isNothing, mapMaybe, maybeToList)

import Data.Hashable

data Edge = Internal {to :: Int} |
  Support {to :: Int, supportSatSet :: OmegaEncodedSet }
  deriving Show

instance Eq Edge where
  p == q = (to p) == (to q)

instance Ord Edge where
  compare p q = compare (to p) (to q)

-- the recordedSatSet is needed to determine whether we have to re-explore a semiconfiguration
data GraphNode state = GraphNode
  { gnId           :: Int
  , iValue         :: Int
  , semiconf       :: (StateId state, Stack state)
  , edges          :: IntMap OmegaEncodedSet -- each (key,value) pair represents an edge. Internal Edges are mapped to empty encoded sets
  , recordedSatSet :: OmegaEncodedSet -- formulae that were holding the last time this node has been explored
  } deriving Show

instance Eq (GraphNode state) where
  p == q =  gnId p ==  gnId q

instance  Ord (GraphNode state) where
  compare p q = compare ( gnId p) ( gnId q)

instance Hashable (GraphNode state) where
  hashWithSalt salt s = hashWithSalt salt $ gnId s

-- some useful renamings
type Key state = (StateId state, Stack state)
type Value state = GraphNode state

-- a basic open-addressing hashtable using linear probing
-- s = thread state, k = key, v = value.
type HashTable s k v = BH.HashTable s k v

data Graph s state = Graph
  { idSeq      :: STRef s Int
  , semiconfsGraphMap :: HashTable s (Int,Int,Int) Int
  , semiconfsGraph :: STRef s (CustoMap s (Value state))
  , sStack     :: GStack s Edge
  , bStack     :: GStack s Int
  , initials   :: STRef s (IntMap OmegaEncodedSet)
  , summaries  :: STRef s [(Int, Key state, OmegaEncodedSet)]
  , bitenc :: OmegaBitencoding state -- different from the usual bitenc
  }

newGraph :: (SatState state, Eq state, Hashable state, Show state)
         => Vector (Key state)
         -> OmegaBitencoding state
         -> ST.ST s (Graph s state)
newGraph iniNodes oBitEnc = do
  newIdSequence <- newSTRef (0 :: Int)
  newGraphMap   <- BH.new
  graph         <- CM.empty
  newSS         <- GS.new
  newBS         <- GS.new
  newInitials   <- newSTRef Map.empty
  newSummaries  <- newSTRef []
  forM_ iniNodes $ \key -> do
    -- some initial nodes may be duplicate
    duplicate <- BH.lookup newGraphMap (decode key)
    when (isNothing duplicate) $ do
      newId <- freshPosId newIdSequence
      BH.insert newGraphMap (decode key) newId
      CM.insert graph newId
        $ GraphNode { gnId = newId
                     , iValue = 0
                     , semiconf = key
                     , edges = Map.empty
                     , recordedSatSet = OE.empty oBitEnc}
      modifySTRef' newInitials (Map.insert newId (OE.empty oBitEnc))
  return $ Graph { idSeq = newIdSequence
                 , semiconfsGraphMap = newGraphMap
                 , semiconfsGraph = graph
                 , sStack = newSS
                 , bStack = newBS
                 , initials = newInitials
                 , summaries = newSummaries
                 , bitenc = oBitEnc
                }

-- some helpers
setgnIValue ::  Int -> GraphNode state -> GraphNode state
setgnIValue new gn  = gn{iValue = new}

resetgnIValue :: GraphNode state -> GraphNode state
resetgnIValue  = setgnIValue 0

initialNodes :: Show state => Graph s state
             -> ST.ST s [(Key state, OmegaEncodedSet)]
initialNodes graph = do
  ini <- readSTRef (initials graph)
  forM (Map.toList ini) $ \(ident, satSet) -> do
    gn <- CM.lookup (semiconfsGraph graph) ident
    return (semiconf gn, satSet)

decodeEdge :: OmegaBitencoding state -> Edge -> OmegaEncodedSet
decodeEdge b (Internal _) = OE.empty b
decodeEdge _ (Support _ suppSatSet) = suppSatSet

insertEdge :: Graph s state -> Int -> Edge -> ST.ST s ()
insertEdge graph ident edge = CM.modify (semiconfsGraph graph) (\g@GraphNode{edges = edges_} -> g{edges = Map.insertWith OE.union (to edge) (decodeEdge (bitenc graph) edge) edges_}) ident
-- end helpers

------------------------------------------------------------------------------------------------------
------------ running the Gabow SCC algorithm with exploring the semiconfiguration graph --------------
------------------------------------------------------------------------------------------------------

addtoPathWith :: Graph s state -> GraphNode state -> Edge -> OmegaEncodedSet -> ST.ST s (GraphNode state)
addtoPathWith graph gn edge newPathSatSet = do
  GS.push (sStack graph) edge
  sSize <- GS.size $ sStack graph
  CM.modify (semiconfsGraph graph) (\g -> g{recordedSatSet = newPathSatSet, iValue = sSize}) (gnId gn)
  GS.push (bStack graph) sSize
  return gn{recordedSatSet = newPathSatSet, iValue = sSize}

updateSccInitialWith :: SatState state
                   => Graph s state
                   -> Key state
                   -> OmegaEncodedSet -- the pathSatSet so far (OE.empty for all initial states in the first search phase)
                   -> ST.ST s Command
updateSccInitialWith graph semiconf_ pathSatSet =
  let -- computing the new set of sat formulae for the current path
      newStateSatSet = OE.encodeSatState (bitenc graph) (getState . fst $ semiconf_)
      cases gn newSCCPathSatSet
       | iValue gn == 0 = addtoPathWith graph gn (Internal (gnId gn)) newSCCPathSatSet >> return (Explore newSCCPathSatSet)
       | iValue gn < 0 && not (recordedSatSet gn `OE.subsumes` newSCCPathSatSet) = addtoPathWith graph gn (Internal (gnId gn)) newSCCPathSatSet >> return (Explore newSCCPathSatSet)
       | iValue gn < 0 = return AlreadyContracted
       | otherwise = error "unexpected case in updateSccInitial"
  in do
  ident <- fromJust <$> BH.lookup (semiconfsGraphMap graph) (decode semiconf_)
  gn <- CM.lookup (semiconfsGraph graph) ident
  cases gn (OE.unions [newStateSatSet, pathSatSet, (recordedSatSet gn)] )

-- determine what to do with a new semiconf
data Command = Explore OmegaEncodedSet | Success | AlreadyContracted

updateSCCs :: (SatState state, Show state)
          => Graph s state
          -> Key state --new semiconf
          -> Maybe OmegaEncodedSet -- the SatSet established on the path so far
          -> Maybe OmegaEncodedSet -- the SatSet of the edge (Nothing if it is not a Support edge) 
          -> ST.ST s Command
updateSCCs graph new_semiconf pathSatSet mSuppSatSet =
  let -- a helper to convert from Booleans to Commands
      convert True = return Success
      convert False = return AlreadyContracted
      -- computing the new set of sat formulae for the current chain
      newStateSatSet = OE.encodeSatState (bitenc graph) (getState . fst $ new_semiconf)
      newPathSatSet = OE.unions (newStateSatSet : catMaybes [pathSatSet, mSuppSatSet])
      -- create a Edge
      createEdge ident Nothing = Internal ident
      createEdge ident (Just csf) = Support{to = ident, supportSatSet=csf}
      -- if it might influence acceptance, push the edge on the stack
      maybePush e@(Internal _ ) = return (Just e)
      maybePush e@Support{} = GS.push (sStack graph) e >> return Nothing
      -- adding new edge to the graph
      addEdge e = do
        lastEdge <- GS.peek (sStack graph)
        insertEdge graph (to lastEdge) e
      -- if the semiconf has never been "seen" by the graph algorithm, then create a new node associated to it
      create_Node = do
        newIdent <- freshPosId $ idSeq graph
        let e = createEdge newIdent mSuppSatSet
        addEdge e
        BH.insert (semiconfsGraphMap graph) (decode new_semiconf) newIdent
        GS.push (sStack graph) e
        sSize <- GS.size $ sStack graph
        CM.insert (semiconfsGraph graph) newIdent (GraphNode{ gnId = newIdent, iValue = sSize, semiconf = new_semiconf, edges = Map.empty, recordedSatSet = newPathSatSet})
        GS.push (bStack graph) sSize
      -- different cases of a semiconf that has already been "seen" by the algorithm
      cases gn e ini newSCCPathSatSet
        | Map.member (gnId gn) ini && (iValue gn == 0)                              = addEdge e >> addtoPathWith graph gn e newSCCPathSatSet >> return (Explore newSCCPathSatSet) -- an initial state that requires exploration
        | (iValue gn <= 0) && not (recordedSatSet gn `OE.subsumes` newSCCPathSatSet) = addEdge e >> addtoPathWith graph gn e newSCCPathSatSet >> return (Explore newSCCPathSatSet) -- we require new exploration because of a non implied satset 
        | (iValue gn == 0)                                                          = addEdge e >> addtoPathWith graph gn e (recordedSatSet gn) >>= sccAlgorithm graph >>= convert -- perform the SCC algorithm, but do not discover new supports
        | (iValue gn < 0)                                                           = addEdge e >> return AlreadyContracted
        | (iValue gn > 0)                                                           = addEdge e >> maybePush e >>= merge graph gn >>= convert
        |  otherwise                                                                = error "at least one condition must be satified"
  in do
    maybeIdent <- BH.lookup (semiconfsGraphMap graph) (decode new_semiconf)
    if isNothing maybeIdent
      then create_Node >> return (Explore newPathSatSet)
      else do
        storedGn <- CM.lookup (semiconfsGraph graph) (fromJust maybeIdent)
        iniSet <- readSTRef (initials graph)
        cases storedGn (createEdge (gnId storedGn) mSuppSatSet) iniSet (OE.unions ((recordedSatSet storedGn) : catMaybes [pathSatSet, mSuppSatSet])) -- recordedSatSet always subsumes newStateSatSet

merge :: (Show state, SatState state)
      => Graph s state
      -> GraphNode state
      -> Maybe Edge
      -> ST.ST s Bool
merge graph gn e = do
    -- contract the B stack, that represents the boundaries between SCCs on the current path (the S stack)
    GS.popWhile_ (bStack graph) (\x -> iValue gn < x)
    -- checking acceptance of the found cycle
    sSize <- GS.size $ sStack graph
    sccEdges <- (maybeToList e ++) <$> GS.multPeek (sStack graph) (sSize - (iValue gn))
    -- these gns might be duplicated, but we lazily don't care, as it is actually faster
    gns <- mapM (CM.lookup (semiconfsGraph graph) . to) sccEdges
    let maybeSupport (Internal _ ) = Nothing
        maybeSupport (Support _ csf) = Just csf
        acceptanceBitVector = OE.unions $ map (OE.encodeSatState (bitenc graph) . getState . fst . semiconf) gns ++ mapMaybe maybeSupport sccEdges
    if OE.isSatisfying acceptanceBitVector
      then return True
      else return False

createComponentGn :: Graph s state -> Key state -> ST.ST s ()
createComponentGn graph key = do
  ident <- fromJust <$> BH.lookup (semiconfsGraphMap graph) (decode key)
  gn <- CM.lookup (semiconfsGraph graph) ident
  createComponent graph gn

createComponent :: Graph s state
                -> GraphNode state
                -> ST.ST s ()
createComponent graph gn = do
  topB <- GS.peek $ bStack graph
  when ((iValue gn) == topB) $ do
      GS.pop_ (bStack graph)
      sSize <- GS.size $ sStack graph
      poppedEdges <- GS.multPop (sStack graph) (sSize - (iValue gn) + 1) -- the last one is to gn
      -- marking the SCC (we don't care about SCCs, so we assign to all of them iValue -1)
      CM.multModify (semiconfsGraph graph) (setgnIValue (-1)) (map to poppedEdges)

toSearchPhase :: (SatState state, Eq state, Hashable state, Show state)
              => Graph s state
              -> IntMap OmegaEncodedSet
              -> ST.ST s ()
toSearchPhase graph newInitials = do
  len <- readSTRef (idSeq graph)
  -- if there are no initials, the new search phase will be aborted immediately
  unless (Map.null newInitials) $ CM.modifyAll (semiconfsGraph graph) resetgnIValue len
  writeSTRef (initials graph) newInitials

toCollapsePhase :: (Show state) => Graph s state
                -> ST.ST s (Bool, IntMap OmegaEncodedSet) -- (are there summaries?, new initials for the next search phase)
toCollapsePhase graph =
  let -- adding a summary to the graph, various cases may occurr
      cases (b,m) gnFrom gnTo chainSatSet unionSatSet
        | ((recordedSatSet gnTo) `OE.subsumes` unionSatSet) &&
          Map.member (gnId gnTo) (edges gnFrom) && (( edges gnFrom Map.! gnId gnTo) `OE.subsumes` chainSatSet) = return (b,m)
        | ((recordedSatSet gnTo) `OE.subsumes` unionSatSet) = insertEdge graph (gnId gnFrom) (Support (gnId gnTo) chainSatSet) >> return (True, m)
        | Map.notMember (gnId gnTo) (edges gnFrom) || not (( (edges gnFrom) Map.!(gnId gnTo)) `OE.subsumes` chainSatSet) = do
            insertEdge graph (gnId gnFrom) (Support (gnId gnTo) chainSatSet)
            return (True, Map.insertWith OE.union (gnId gnTo) unionSatSet m)
        | Map.member (gnId gnTo) m = return (b,m)
        | otherwise = error ("unexpected case in toCollapsePhase" ++ show gnFrom ++ "\n\n---\n" ++ show gnTo ++ "\n\n---\n" ++ OE.showOmegaEncoding (bitenc graph) chainSatSet ++ "\nEdge to add: " ++ show chainSatSet ++ "\n\n\nLc + edge: " ++ show unionSatSet)
      resolveSummary (b, m) (gnId_, to_semiconf, chainSatSet) = do
        maybeIdent <- BH.lookup (semiconfsGraphMap graph) (decode to_semiconf)
        gnFrom <- CM.lookup (semiconfsGraph graph) gnId_
        if isNothing maybeIdent
          then do -- the destination does not exist in the graph
            newIdent <- freshPosId $ idSeq graph
            BH.insert (semiconfsGraphMap graph) (decode to_semiconf) newIdent
            CM.insert (semiconfsGraph graph) newIdent (GraphNode{ gnId = newIdent, iValue = 0, semiconf = to_semiconf, edges = Map.empty, recordedSatSet = OE.empty (bitenc graph)})
            insertEdge graph gnId_ (Support newIdent chainSatSet)
            return (True, Map.insertWith OE.union newIdent (OE.union chainSatSet (recordedSatSet gnFrom)) m)
          else do
            gnTo <- CM.lookup (semiconfsGraph graph) (fromJust maybeIdent)
            cases (b,m) gnFrom gnTo chainSatSet (OE.union chainSatSet (recordedSatSet gnFrom))
  in do
    (mustCollapse, newInitials) <- foldM resolveSummary (False, Map.empty) =<< readSTRef (summaries graph)
    if not mustCollapse
      then return (False, Map.empty)
      else do
        writeSTRef (summaries graph) []
        len <- readSTRef (idSeq graph)
        CM.modifyAll (semiconfsGraph graph) resetgnIValue len
        return (True, newInitials)

insertSummary :: Graph s state
                -> Key state
                -> Key state
                -> OmegaEncodedSet -- the current pathSatSet 
                -> ST.ST s ()
insertSummary graph fromSemiconf toSemiconf pathSatSet = do
  gnId_ <- fromJust <$> BH.lookup (semiconfsGraphMap graph) (decode fromSemiconf)
  modifySTRef' (summaries graph) $ \l -> (gnId_, toSemiconf, pathSatSet):l

--------------------------------------------------------
--- running the Gabow SCC algorithm only ---------------
--------------------------------------------------------

updateSccInitial :: (SatState state, Show state)
                   => Graph s state
                   -> Key state
                   -> ST.ST s Bool
updateSccInitial graph semiconf_ =
  let cases gn
       | iValue gn == 0 = addtoPath graph gn (Internal (gnId gn)) >>= sccAlgorithm graph
       | iValue gn < 0  = return False
       | otherwise = error "unexpected case in updateSccInitial"
  in do
    ident <- fromJust <$> BH.lookup (semiconfsGraphMap graph) (decode semiconf_)
    gn <- CM.lookup (semiconfsGraph graph) ident
    cases gn

addtoPath :: Graph s state -> GraphNode state -> Edge -> ST.ST s (GraphNode state)
addtoPath graph gn edge  = do
  GS.push (sStack graph) edge
  sSize <- GS.size $ sStack graph
  CM.modify (semiconfsGraph graph) (\g -> g{iValue = sSize }) (gnId gn)
  GS.push (bStack graph) sSize
  return gn{iValue = sSize}

sccAlgorithm :: (Show state, SatState state)
               => Graph s state
               -> GraphNode state
               -> ST.ST s Bool
sccAlgorithm graph gn =
  let
    -- if it might influence acceptance, push the edge on the stack
    maybePush e@(Internal _ ) = return (Just e)
    maybePush e@Support{} = GS.push (sStack graph) e >> return Nothing
    -- different cases of the Gabow SCC algorithm
    cases e nextGn
      | (iValue nextGn == 0) = addtoPath graph nextGn e >>= sccAlgorithm graph
      | (iValue nextGn < 0)  = return False
      | (iValue nextGn > 0)  = maybePush e >>= merge graph nextGn
      | otherwise = error "unreachable error"
  in do
  success <-  foldM (\acc (ident, supportEdge) -> if acc
                                                   then return True
                                                   else CM.lookup (semiconfsGraph graph) ident >>= cases (Support ident supportEdge)
                    )
                    False
                    (Map.toList $ edges gn)
  createComponent graph gn
  return success


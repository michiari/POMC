{- |
   Module      : Pomc.Satisfiability
   Copyright   : 2020 Michele Chiari
   License     : MIT
   Maintainer  : Michele Chiari
-}

module Pomc.Satisfiability ( SatState(..)
                           , Delta(..)
                           , isEmpty
                           , isSatisfiable
                           , isSatisfiableGen
                           , toInputTrace
                           , showTrace
                           ) where

import Pomc.Prop (Prop(..))
import Pomc.Prec (Prec(..), StructPrecRel)
import Pomc.Potl (Formula)
import Pomc.Check (Input, EncPrecFunc, State(..), makeOpa, showState, showAtom)
import Pomc.PropConv (APType, convPropLabels)
import Pomc.Data (PropSet, BitEncoding, extractInput, decodeInput)

import Control.Monad (foldM)
import Control.Monad.ST (ST)
import qualified Control.Monad.ST as ST
import Data.STRef (STRef, newSTRef, readSTRef, writeSTRef, modifySTRef')
import Data.Maybe

import Data.Set (Set)
import qualified Data.Set as Set

import Data.Hashable
import qualified Data.HashTable.ST.Basic as BH
import qualified Data.HashTable.Class as H

import qualified Data.Vector.Mutable as MV
import Data.Vector (Vector)
import qualified Data.Vector as V

type HashTable s k v = BH.HashTable s k v


-- Map to sets
type SetMap s v = MV.MVector s (Set v)

insertSM :: (Ord v) => STRef s (SetMap s v) -> StateId state -> v -> ST.ST s ()
insertSM smref stateId val = do
  sm <- readSTRef smref
  let len = MV.length sm
      sid = getId stateId
  if sid < len
    then MV.unsafeModify sm (Set.insert val) sid
    else let newLen = computeLen len sid

             computeLen size idx | idx < size = size
                                 | otherwise = computeLen (size*2) idx
         in do { grown <- MV.grow sm (newLen-len)
               ; mapM_ (\i -> MV.unsafeWrite grown i Set.empty) [len..(newLen-1)]
               ; MV.unsafeModify grown (Set.insert val) sid
               ; writeSTRef smref grown
               }

lookupSM :: STRef s (SetMap s v) -> StateId state -> ST.ST s (Set v)
lookupSM smref stateId = do
  sm <- readSTRef smref
  let sid = getId stateId
  if sid < MV.length sm
    then MV.unsafeRead sm sid
    else return Set.empty

memberSM :: (Ord v) => STRef s (SetMap s v) -> StateId state -> v -> ST.ST s Bool
memberSM smref stateId val = do
  vset <- lookupSM smref stateId
  return $ val `Set.member` vset

emptySM :: ST.ST s (STRef s (SetMap s v))
emptySM = do
  sm <- MV.replicate 4 Set.empty
  newSTRef sm


-- State class for satisfiability
class SatState state where
  getSatState :: state -> State
  getStateProps :: BitEncoding -> state -> Input

instance SatState State where
  getSatState = id
  {-# INLINABLE getSatState #-}

  getStateProps bitencoding s = extractInput bitencoding (current $ s)
  {-# INLINABLE getStateProps #-}


-- States with unique IDs
data StateId state = StateId { getId :: !Int,
                               getState :: state } deriving (Show)

instance Eq (StateId state) where
  p == q = getId p == getId q

instance Ord (StateId state) where
  compare p q = compare (getId p) (getId q)

instance Hashable (StateId state) where
  hashWithSalt salt s = hashWithSalt salt $ getId s

data SIdGen s state = SIdGen
  { idSequence :: STRef s Int
  , stateToId :: HashTable s state (StateId state)
  }

initSIdGen :: ST.ST s (SIdGen s state)
initSIdGen = do
  newIdSequence <- newSTRef (0 :: Int)
  newStateToId <- H.new
  return $ SIdGen { idSequence = newIdSequence,
                    stateToId = newStateToId }

wrapState :: (Eq state, Hashable state)
          => SIdGen s state
          -> state
          -> ST.ST s (StateId state)
wrapState sig q = do
  qwrapped <- H.lookup (stateToId sig) q
  if isJust qwrapped
    then return $ fromJust qwrapped
    else do
    let idSeq = idSequence sig
    newId <- readSTRef idSeq
    modifySTRef' idSeq (+1)
    let newQwrapped = StateId newId q
    H.insert (stateToId sig) q newQwrapped
    return newQwrapped

wrapStates :: (Eq state, Hashable state)
           => SIdGen s state
           -> [state]
           -> ST.ST s (Vector (StateId state))
wrapStates sig states = do
  wrappedList <- V.mapM (wrapState sig) (V.fromList states)
  return wrappedList


-- Stack symbol
type Stack state = Maybe (Input, StateId state)

data Globals s state = Globals
  { sIdGen :: SIdGen s state
  , visited :: STRef s (SetMap s (Stack state))
  , suppStarts :: STRef s (SetMap s (Stack state))
  , suppEnds :: STRef s (SetMap s (StateId state))
  }

data Delta state = Delta
  { bitenc :: BitEncoding
  , prec :: EncPrecFunc
  , deltaPush :: state -> Input -> [state]
  , deltaShift :: state -> Input -> [state]
  , deltaPop :: state -> state -> [state]
  }

-- Begin debugging stuff
data TraceType = Push | Shift | Pop | Summary | Found deriving (Eq, Show)
type TraceId state = [(TraceType, StateId state, Stack state)]
type Trace state = [(TraceType, state, Maybe (Input, state))]

unIdTrace :: TraceId state -> Trace state
unIdTrace trace =
  map (\(moveType, q, g) ->
         (moveType, getState q, fmap (\(b, r) -> (b, getState r)) g)) trace

toInputTrace :: (SatState state) => BitEncoding -> Trace state -> [(state, PropSet)]
toInputTrace be trace = foldr foldInput [] trace
  where foldInput (moveType, q, _) rest
          | moveType == Push || moveType == Shift =
            (q, stateToInput q) : rest
          | moveType == Summary =
            (q, Set.empty) : rest
          | moveType == Found =
            (q, Set.singleton End) : rest
          | otherwise = rest
        stateToInput q =
          (decodeInput be) . (extractInput be) . current . getSatState $ q

showTrace :: (SatState state, Show state, Show a)
          => BitEncoding
          -> (APType -> a)
          -> Trace state
          -> String
showTrace be transAP trace = concatMap showMove trace
  where showMove (moveType, q, g) =
          show moveType     ++ ":\nRaw State:\n" ++
          show q ++ "\nCheck State:\n" ++
          showState be transAP (getSatState q) ++ "\nStack:\n" ++
          showStack g ++ "\n\n"
        showStack (Just (b, r)) =
          showAtom be transAP b ++ "\n" ++
          show r ++ "\n" ++
          showState be transAP (getSatState r)
        showStack Nothing = "Bottom"
-- End debugging stuff

reach :: (SatState state, Eq state, Hashable state, Show state)
      => (StateId state -> Bool)
      -> (Stack state -> Bool)
      -> Globals s state
      -> Delta state
      -> StateId state
      -> Stack state
      -> TraceId state
      -> ST s (Bool, TraceId state)
reach isDestState isDestStack globals delta q g trace = do
  alreadyVisited <- memberSM (visited globals) q g
  if alreadyVisited
    then return (False, [])
    else do
    insertSM (visited globals) q g
    let qState = getState q
        precRel = (prec delta) (fst . fromJust $ g) (current . getSatState $ qState)
        cases
          | (isDestState q) && (isDestStack g) = return (True, (Found, q, g) : trace)

          | (isNothing g) || precRel == Just Yield =
            reachPush isDestState isDestStack globals delta q g qState trace

          | precRel == Just Equal =
            reachShift isDestState isDestStack globals delta q g qState trace

          | precRel == Just Take =
            reachPop isDestState isDestStack globals delta q g qState trace

          | otherwise = return (False, [])
    cases


reachPush :: (SatState state, Eq state, Hashable state, Show state)
          => (StateId state -> Bool)
          -> (Stack state -> Bool)
          -> Globals s state
          -> Delta state
          -> StateId state
          -> Stack state
          -> state
          -> TraceId  state
          -> ST s (Bool, TraceId state)
reachPush isDestState isDestStack globals delta q g qState trace =
  let qProps = getStateProps (bitenc delta) qState
      doPush res@(True, _) _ = return res
      doPush (False, _) p = do
        insertSM (suppStarts globals) q g
        reach isDestState isDestStack globals delta p (Just (qProps, q)) ((Push, q, g) : trace)
  in do
    newStates <- wrapStates (sIdGen globals) $ (deltaPush delta) qState qProps
    res@(pushReached, _) <- V.foldM' doPush (False, []) newStates
    if pushReached
      then return res
      else do
      currentSuppEnds <- lookupSM (suppEnds globals) q
      foldM (\acc s -> if fst acc
                       then return acc
                       else reach isDestState isDestStack globals delta s g ((Summary, q, g) : trace))
        (False, [])
        currentSuppEnds


reachShift :: (SatState state, Eq state, Hashable state, Show state)
           => (StateId state -> Bool)
           -> (Stack state -> Bool)
           -> Globals s state
           -> Delta state
           -> StateId state
           -> Stack state
           -> state
           -> TraceId state
           -> ST s (Bool, TraceId state)
reachShift isDestState isDestStack globals delta q g qState trace =
  let qProps = getStateProps (bitenc delta) qState
      doShift res@(True, _) _ = return res
      doShift (False, _) p =
        reach isDestState isDestStack globals delta p (Just (qProps, (snd . fromJust $ g))) ((Shift, q, g) : trace)
  in do
    newStates <- wrapStates (sIdGen globals) $ (deltaShift delta) qState qProps
    V.foldM' doShift (False, []) newStates


reachPop :: (SatState state, Eq state, Hashable state, Show state)
         => (StateId state -> Bool)
         -> (Stack state -> Bool)
         -> Globals s state
         -> Delta state
         -> StateId state
         -> Stack state
         -> state
         -> TraceId state
         -> ST s (Bool, TraceId state)
reachPop isDestState isDestStack globals delta q g qState trace =
  let doPop res@(True, _) _ = return res
      doPop (False, _) p =
        let r = snd . fromJust $ g
            closeSupports res@(True, _) _ = return res
            closeSupports (False, _) g'
              | isNothing g' ||
                ((prec delta) (fst . fromJust $ g') (current . getSatState . getState $ r)) == Just Yield
              = reach isDestState isDestStack globals delta p g' ((Pop, q, g) : trace)
              | otherwise = return (False, [])
        in do
          insertSM (suppEnds globals) r p
          currentSuppStarts <- lookupSM (suppStarts globals) r
          foldM closeSupports (False, []) currentSuppStarts
  in do
    newStates <- wrapStates (sIdGen globals) $
                 (deltaPop delta) qState (getState . snd . fromJust $ g)
    V.foldM' doPop (False, []) newStates


isEmpty :: (SatState state, Eq state, Hashable state, Show state)
        => Delta state
        -> [state]
        -> (state -> Bool)
        -> (Bool, Trace state)
isEmpty delta initials isFinal =
  let (accepting, trace) = ST.runST $ do
        newSig <- initSIdGen
        emptyVisited <- emptySM
        emptySuppStarts <- emptySM
        emptySuppEnds <- emptySM
        let globals = Globals { sIdGen = newSig
                              , visited = emptyVisited
                              , suppStarts = emptySuppStarts
                              , suppEnds = emptySuppEnds
                              }
        initialsId <- wrapStates newSig initials
        foldM (\acc q -> if fst acc
                         then return acc
                         else reach (isFinal . getState) isNothing globals delta q Nothing [])
          (False, [])
          initialsId
  in (not accepting, unIdTrace $ reverse trace)

isSatisfiable :: Formula APType
              -> ([Prop APType], [Prop APType])
              -> [StructPrecRel APType]
              -> (Bool, [PropSet])
isSatisfiable phi ap sprs =
  let (be, precf, initials, isFinal, dPush, dShift, dPop) = makeOpa phi ap sprs
      delta = Delta
        { bitenc = be
        , prec = precf
        , deltaPush = (\q _ -> dPush q Nothing)
        , deltaShift = (\q _ -> dShift q Nothing)
        , deltaPop = dPop
        }
      (empty, trace) = isEmpty delta initials isFinal
  in (not empty, map snd $ toInputTrace be trace)

isSatisfiableGen :: (Ord a)
                 => Formula a
                 -> ([Prop a], [Prop a])
                 -> [StructPrecRel a]
                 -> (Bool, [Set (Prop a)])
isSatisfiableGen phi ap precf =
  let (tphi, tap, tprecr, transInv) = convPropLabels phi ap precf
      (sat, trace) = isSatisfiable tphi tap tprecr
  in (sat, map (Set.map (fmap transInv)) trace)

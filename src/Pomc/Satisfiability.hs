{-# LANGUAGE DeriveGeneric, DeriveAnyClass #-}

{- |
   Module      : Pomc.Satisfiability
   Copyright   : 2020 Michele Chiari
   License     : MIT
   Maintainer  : Michele Chiari
-}

module Pomc.Satisfiability (
                             SatState(..)
                           , Delta(..)
                           , isEmpty
                           , isSatisfiable
                           , isSatisfiableGen
                           ) where

import Pomc.Prop (Prop(..))
import Pomc.Prec (Prec(..), StructPrecRel)
import Pomc.Check (Checkable(..), Input, EncPrecFunc, State(..), makeOpa)
import Pomc.RPotl (Formula(Atomic))
import Pomc.PropConv (APType, convPropLabels)
import Pomc.Data (BitEncoding, extractInput)
import qualified Pomc.Data as D (member)

import Control.Monad (foldM)
import Control.Monad.ST (ST)
import qualified Control.Monad.ST as ST
import Control.DeepSeq (NFData, force)
import GHC.Generics (Generic)
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

--import Debug.Trace (trace)

debug :: String -> ST s Bool -> ST s Bool
debug _ x = x
--debug msg r = fmap traceTrue r
--  where traceTrue False = False
--        traceTrue True = trace msg True


type HashTable s k v = BH.HashTable s k v


-- Map to sets
type SetMap s v = MV.MVector s (Set v)

insertSM :: (Ord v, NFData v) => STRef s (SetMap s v) -> StateId state -> v -> ST.ST s ()
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
                               getState :: state } deriving (Show, Generic, NFData)

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

wrapStates :: (Eq state, Hashable state, NFData state)
           => SIdGen s state
           -> [state]
           -> ST.ST s (Vector (StateId state))
wrapStates sig states = do
  wrappedList <- mapM (wrapState sig) states
  return $! V.fromList wrappedList


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

getSidProps :: (SatState state) => BitEncoding -> StateId state -> Input
getSidProps bitencoding s = (getStateProps bitencoding) . getState $ s

popFirst :: (SatState state) => BitEncoding -> [state] -> [state]
popFirst bitencoding states =
  let (endStates, otherPop, others) = foldl partitionStates ([], [], []) states
  in endStates ++ otherPop ++ others
  where isMustPop s = let ss = getSatState s
                      in not (mustPush ss || mustShift ss)
        isEndState s = D.member bitencoding (Atomic End) (current . getSatState $ s)

        partitionStates (endStates, otherPop, others) s
          | isMustPop s = if isEndState s
                          then (s:endStates, otherPop, others)
                          else (endStates, s:otherPop, others)
          | otherwise = (endStates, otherPop, s:others)

reach :: (SatState state, Eq state, Hashable state, Show state, NFData state)
      => (StateId state -> Bool)
      -> (Stack state-> Bool)
      -> Globals s state
      -> Delta state
      -> StateId state
      -> Stack state
      -> ST s Bool
reach isDestState isDestStack globals delta q g = do
  alreadyVisited <- memberSM (visited globals) q g
  if alreadyVisited
    then return False
    else do
    insertSM (visited globals) q g
    let be = bitenc delta
        qProps = getSidProps be q
        qState = getState q
        cases
          | (isDestState q) && (isDestStack g) = debug ("End: q = " ++ show q ++ "\ng = " ++ show g ++ "\n") $ return True
          | (isNothing g) || ((prec delta) (fst . fromJust $ g) qProps == Just Yield) = do
              newStates <- wrapStates (sIdGen globals) $ popFirst be ((deltaPush delta) qState qProps)
              V.foldM' (reachPush isDestState isDestStack globals delta q g) False newStates
          | ((prec delta) (fst . fromJust $ g) qProps == Just Equal) = do
              newStates <- wrapStates (sIdGen globals) $ popFirst be ((deltaShift delta) qState qProps)
              let reachShift acc p
                    = if acc
                      then return True
                      else debug ("Shift: q = " ++ show q ++ "\ng = " ++ show g ++ "\n") $
                           reach isDestState isDestStack globals delta p (Just (qProps, (snd . fromJust $ g)))
              V.foldM' reachShift False newStates
          | ((prec delta) (fst . fromJust $ g) qProps == Just Take) = do
              newStates <- wrapStates (sIdGen globals) $ popFirst be ((deltaPop delta) qState (getState . snd . fromJust $ g))
              V.foldM' (reachPop isDestState isDestStack globals delta q g) False newStates
          | otherwise = return False
    cases

reachPush :: (SatState state, Eq state, Hashable state, Show state, NFData state)
          => (StateId state -> Bool)
          -> (Stack state -> Bool)
          -> Globals s state
          -> Delta state
          -> StateId state
          -> Stack state
          -> Bool
          -> StateId state
          -> ST s Bool
reachPush _ _ _ _ _ _ True _ = return True
reachPush isDestState isDestStack globals delta q g False p = do
  insertSM (suppStarts globals) q g
  alreadyVisited <- memberSM (visited globals) p (Just (getSidProps (bitenc delta) q, p))
  if not alreadyVisited
    then debug ("Push: q = " ++ show q ++ "\ng = " ++ show g ++ "\n") $
         reach isDestState isDestStack globals delta p (Just (getSidProps (bitenc delta) q, q))
    else do
    currentSuppEnds <- lookupSM (suppEnds globals) q
    foldM (\acc s -> if acc
                     then return True
                     else debug ("Push (summary): q = " ++ show q ++ "\ng = " ++ show g ++ "\np = "++ show p ++ "\ns = " ++ show s) $
                          reach isDestState isDestStack globals delta s g)
      False
      currentSuppEnds

reachPop :: (SatState state, Eq state, Hashable state, Show state, NFData state)
         => (StateId state -> Bool)
         -> (Stack state -> Bool)
         -> Globals s state
         -> Delta state
         -> StateId state
         -> Stack state
         -> Bool
         -> StateId state
         -> ST s Bool
reachPop _ _ _ _ _ _ True _ = return True
reachPop isDestState isDestStack globals delta q g False p = do
  let r = snd . fromJust $ g
  insertSM (suppEnds globals) r p
  currentSuppStarts <- lookupSM (suppStarts globals) r
  foldM (\acc g' -> if acc
                    then return True
                    else debug ("Pop: q = " ++ show q ++ "\ng = " ++ show g ++ "\n") $
                         reach isDestState isDestStack globals delta p g')
    False
    (Set.filter (\g' -> isNothing g' ||
                        ((prec delta) (fst . fromJust $ g') (getSidProps (bitenc delta) r)) == Just Yield)
      currentSuppStarts)


isEmpty :: (SatState state, Eq state, Hashable state, Show state, NFData state)
        => Delta state
        -> [state]
        -> (state -> Bool)
        -> Bool
isEmpty delta initials isFinal = not $
  ST.runST (do
               newSig <- initSIdGen
               emptyVisited <- emptySM
               emptySuppStarts <- emptySM
               emptySuppEnds <- emptySM
               let globals = Globals { sIdGen = newSig
                                     , visited = emptyVisited
                                     , suppStarts = emptySuppStarts
                                     , suppEnds = emptySuppEnds
                                     }
                 in do
                 initialsId <- wrapStates newSig initials
                 foldM (\acc q -> if acc
                                  then return True
                                  else (reach (isFinal . getState) isNothing globals delta q Nothing))
                   False
                   initialsId)

isSatisfiable :: (Checkable f)
              => f APType
              -> ([Prop APType], [Prop APType])
              -> [StructPrecRel APType]
              -> Bool
isSatisfiable phi ap sprs =
  let (be, precf, initials, isFinal, dPush, dShift, dPop) = makeOpa phi ap sprs
      delta = Delta
        { bitenc = be
        , prec = precf
        , deltaPush = dPush
        , deltaShift = dShift
        , deltaPop = dPop
        }
  in not $ isEmpty delta initials isFinal

isSatisfiableGen :: (Checkable f, Ord a)
                 => f a
                 -> ([Prop a], [Prop a])
                 -> [StructPrecRel a]
                 -> Bool
isSatisfiableGen phi ap precf =
  let (tphi, tap, tprecr) = convPropLabels (toReducedPotl phi) ap precf
  in isSatisfiable tphi tap tprecr


{- |
   Module      : Pomc.Satisfiability
   Copyright   : 2020 Michele Chiari
   License     : MIT
   Maintainer  : Michele Chiari
-}

module Pomc.Satisfiability (
                             isSatisfiable
                           , isSatisfiableGen
                           , Input
                           ) where

import Pomc.Prop (Prop(..))
import Pomc.Prec (Prec(..), StructPrecRel, PrecFunc, fromStructPR)
import Pomc.Check (Checkable(..), Input, Atom(..), State(..), makeOpa)
import Pomc.RPotl (Formula(Atomic), atomic)
import Pomc.PropConv (APType, convPropLabels)

import Control.Monad (foldM)
import Control.Monad.ST (ST)
import qualified Control.Monad.ST as ST
import Data.STRef (STRef, newSTRef, readSTRef, modifySTRef')

import Data.Maybe
import Data.List (partition)

import Data.Set (Set)
import qualified Data.Set as Set

import Data.Hashable
import qualified Data.HashTable.ST.Basic as BH
import qualified Data.HashTable.Class as H

--import Debug.Trace (trace)

debug :: String -> ST s Bool -> ST s Bool
debug _ x = x
-- debug msg r = fmap traceTrue r
--   where traceTrue False = False
--         traceTrue True = trace msg True


type HashTable s k v = BH.HashTable s k v

memberHT :: (Eq k, Hashable k) => HashTable s k v -> k -> ST.ST s Bool
memberHT ht key = do
  val <- H.lookup ht key
  return $ isJust val

-- Map to lists
type SetMap s k v = HashTable s k (Set v)

insertSM :: (Eq k, Hashable k, Ord v) => SetMap s k v -> k -> v -> ST.ST s ()
insertSM lm key val = H.mutate lm key consVal
  where consVal Nothing = (Just $ Set.singleton val, ())
        consVal (Just vals) = (Just $ Set.insert val vals, ())

lookupSM :: (Eq k, Hashable k) => SetMap s k v -> k -> ST.ST s (Set v)
lookupSM lm key = do
  val <- H.lookup lm key
  return $ maybeList val
    where maybeList Nothing = Set.empty
          maybeList (Just l) = l

emptySM :: ST.ST s (SetMap s k v)
emptySM = H.new


-- States with unique IDs
data StateId = StateId { getId :: !Int,
                         getState :: State } deriving (Show)

instance Eq StateId where
  p == q = getId p == getId q

instance Ord StateId where
  compare p q = compare (getId p) (getId q)

instance Hashable StateId where
  hashWithSalt salt s = hashWithSalt salt $ getId s

data SIdGen s = SIdGen { idSequence :: STRef s Int,
                         stateToId :: HashTable s State Int }

initSIdGen :: ST.ST s (SIdGen s)
initSIdGen = do
  newIdSequence <- newSTRef (0 :: Int)
  newStateToId <- H.new
  return $ SIdGen { idSequence = newIdSequence,
                    stateToId = newStateToId }

wrapState :: SIdGen s -> State -> ST.ST s StateId
wrapState sig q = do
  qid <- H.lookup (stateToId sig) q
  if isJust qid
    then return $ StateId (fromJust qid) q
    else do
    let idSeq = idSequence sig
    newId <- readSTRef idSeq
    modifySTRef' idSeq (+1)
    H.insert (stateToId sig) q newId
    return $ StateId newId q

wrapStates :: SIdGen s -> [State] -> ST.ST s [StateId]
wrapStates sig states = mapM (wrapState sig) states


-- Stack symbol
type Stack = Maybe (Input, StateId)

data Globals s = Globals { sIdGen :: SIdGen s,
                           visited :: HashTable s (StateId, Stack) (),
                           suppStarts :: SetMap s (StateId) (Stack),
                           suppEnds :: SetMap s (StateId) (StateId) }
data Delta = Delta { prec :: PrecFunc APType,
                     deltaPush :: State -> Input -> [State],
                     deltaShift :: State -> Input -> [State],
                     deltaPop :: State -> State -> [State] }

getStateProps :: State -> Input
getStateProps s = Set.map (\(Atomic p) -> p) $ Set.filter atomic (atomFormulaSet . current $ s)

getProps :: StateId -> Input
getProps s = getStateProps . getState $ s

popFirst :: [State] -> [State]
popFirst states =
  let (popStates, others) = partition (\s -> not (mustPush s || mustShift s)) states
      (endStates, otherPop) = partition (\s -> Set.member (Atomic End) (atomFormulaSet . current $ s)) popStates
  in endStates ++ otherPop ++ others

reach :: (StateId -> Bool)
      -> (Stack -> Bool)
      -> Globals s
      -> Delta
      -> StateId
      -> Stack
      -> ST s Bool
reach isDestState isDestStack globals delta q g = do
  alreadyVisited <- memberHT (visited globals) (q, g)
  if alreadyVisited
    then return False
    else do
    H.insert (visited globals) (q, g) ()
    let qProps = getProps q
        qState = getState q
        cases
          | (isDestState q) && (isDestStack g) = debug ("End: q = " ++ show q ++ "\ng = " ++ show g ++ "\n") $ return True
          | (isNothing g) || ((prec delta) (fst . fromJust $ g) qProps == Just Yield) = do
              newStates <- wrapStates (sIdGen globals) $ popFirst ((deltaPush delta) qState qProps)
              foldM (reachPush isDestState isDestStack globals delta q g) False newStates
          | ((prec delta) (fst . fromJust $ g) qProps == Just Equal) = do
              newStates <- wrapStates (sIdGen globals) $ popFirst ((deltaShift delta) qState qProps)
              let reachShift acc p
                    = if acc
                      then return True
                      else debug ("Shift: q = " ++ show q ++ "\ng = " ++ show g ++ "\n") $
                           reach isDestState isDestStack globals delta p (Just (qProps, (snd . fromJust $ g)))
              foldM reachShift False newStates
          | ((prec delta) (fst . fromJust $ g) qProps == Just Take) = do
              newStates <- wrapStates (sIdGen globals) $ popFirst ((deltaPop delta) qState (getState . snd . fromJust $ g))
              foldM (reachPop isDestState isDestStack globals delta q g) False newStates
          | otherwise = return False
    cases

reachPush :: (StateId -> Bool)
          -> (Stack -> Bool)
          -> Globals s
          -> Delta
          -> StateId
          -> Stack
          -> Bool
          -> StateId
          -> ST s Bool
reachPush _ _ _ _ _ _ True _ = return True
reachPush isDestState isDestStack globals delta q g False p = do
  insertSM (suppStarts globals) q g
  alreadyVisited <- memberHT (visited globals) (p, Just (getProps q, p))
  if not alreadyVisited
    then debug ("Push: q = " ++ show q ++ "\ng = " ++ show g ++ "\n") $
         reach isDestState isDestStack globals delta p (Just (getProps q, q))
    else do
    currentSuppEnds <- lookupSM (suppEnds globals) q
    foldM (\acc s -> if acc
                     then return True
                     else debug ("Push (summary): q = " ++ show q ++ "\ng = " ++ show g ++ "\np = "++ show p ++ "\ns = " ++ show s) $
                          reach isDestState isDestStack globals delta s g)
      False
      currentSuppEnds

reachPop :: (StateId -> Bool)
         -> (Stack -> Bool)
         -> Globals s
         -> Delta
         -> StateId
         -> Stack
         -> Bool
         -> StateId
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
                        ((prec delta) (fst . fromJust $ g') (getProps r)) == Just Yield)
      currentSuppStarts)


isEmpty :: Delta
        -> [State]
        -> (State -> Bool)
        -> Bool
isEmpty delta initials isFinal = not $
  ST.runST (do
               newSig <- initSIdGen
               emptyVisited <- H.new
               emptySuppStarts <- emptySM
               emptySuppEnds <- emptySM
               let globals = Globals { sIdGen = newSig,
                                       visited = emptyVisited,
                                       suppStarts = emptySuppStarts,
                                       suppEnds = emptySuppEnds }
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
              -> PrecFunc APType
              -> Bool
isSatisfiable phi ap precf =
  let (initials, isFinal, dPush, dShift, dPop) = makeOpa phi ap precf
      delta = Delta { prec = precf,
                      deltaPush = dPush,
                      deltaShift = dShift,
                      deltaPop = dPop }
  in not $ isEmpty delta initials isFinal

isSatisfiableGen :: (Checkable f, Ord a)
                 => f a
                 -> ([Prop a], [Prop a])
                 -> [StructPrecRel a]
                 -> Bool
isSatisfiableGen phi ap precf =
  let (tphi, tap, tprecr) = convPropLabels (toReducedPotl phi) ap precf
  in isSatisfiable tphi tap (fromStructPR tprecr)


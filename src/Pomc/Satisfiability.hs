{- |
   Module      : Pomc.Satisfiability
   Copyright   : 2020 Michele Chiari
   License     : MIT
   Maintainer  : Michele Chiari
-}

module Pomc.Satisfiability (
                             isSatisfiable
                           , isSatisfiablePotlV2
                           , Input
                           ) where

import Pomc.Prop (Prop(..))
import Pomc.Prec (Prec(..), StructPrecRel, PrecFunc, fromStructPR)
import Pomc.Check (Checkable(..), Atom(..), State(..), makeOpa, closure)
import Pomc.RPotl (Formula(Atomic), atomic)
import qualified Pomc.PotlV2 as P2

import Control.Monad (foldM)
import Control.Monad.ST (ST)
import qualified Control.Monad.ST as ST
import Data.STRef (STRef, newSTRef, readSTRef, modifySTRef')

import Data.Maybe
import Data.List (nub, partition)

import Data.Set (Set)
import qualified Data.Set as Set

import qualified Data.Map as Map

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


-- Input symbol
type Input a = Set (Prop a)


-- States with unique IDs
data StateId a = StateId { getId :: !Int,
                           getState :: State a } deriving (Show)

instance Eq (StateId a) where
  p == q = getId p == getId q

instance Ord (StateId a) where
  compare p q = compare (getId p) (getId q)

instance Hashable (StateId a) where
  hashWithSalt salt s = hashWithSalt salt $ getId s

data SIdGen s a = SIdGen { idSequence :: STRef s Int,
                           stateToId :: HashTable s (State a) Int }

initSIdGen :: ST.ST s (SIdGen s a)
initSIdGen = do
  newIdSequence <- newSTRef (0 :: Int)
  newStateToId <- H.new
  return $ SIdGen { idSequence = newIdSequence,
                    stateToId = newStateToId }

wrapState :: (Eq a, Hashable a) => SIdGen s a -> State a -> ST.ST s (StateId a)
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

wrapStates :: (Eq a, Hashable a) => SIdGen s a -> [State a] -> ST.ST s [StateId a]
wrapStates sig states = mapM (wrapState sig) states


-- Stack symbol
type Stack a = Maybe (Input a, StateId a)

data Globals s a = Globals { sIdGen :: SIdGen s a,
                             visited :: HashTable s (StateId a, Stack a) (),
                             suppStarts :: SetMap s (StateId a) (Stack a),
                             suppEnds :: SetMap s (StateId a) (StateId a) }
data Delta a = Delta { prec :: PrecFunc a,
                       deltaPush :: State a -> Input a -> [State a],
                       deltaShift :: State a -> Input a -> [State a],
                       deltaPop :: State a -> State a -> [State a] }

getStateProps :: (Ord a, Hashable a) => State a -> Input a
getStateProps s = Set.map (\(Atomic p) -> p) $ Set.filter atomic (atomFormulaSet . current $ s)

getProps :: (Ord a, Hashable a) => StateId a -> Input a
getProps s = getStateProps . getState $ s

popFirst :: (Ord a, Hashable a) => [State a] -> [State a]
popFirst states =
  let (popStates, others) = partition (\s -> not (mustPush s || mustShift s)) states
      (endStates, otherPop) = partition (\s -> Set.member (Atomic End) (atomFormulaSet . current $ s)) popStates
  in endStates ++ otherPop ++ others

reach :: (Ord a, Eq a, Hashable a, Show a)
      => (StateId a -> Bool)
      -> (Stack a -> Bool)
      -> Globals s a
      -> Delta a
      -> StateId a
      -> Stack a
      -> ST s Bool
reach isDestState isDestStack globals delta q g = do
  alreadyVisited <- memberHT (visited globals) (q, g)
  if alreadyVisited
    then return False
    else do
    H.insert (visited globals) (q, g) ()
    let cases
          | (isDestState q) && (isDestStack g) = debug ("End: q = " ++ show q ++ "\ng = " ++ show g ++ "\n") $ return True
          | (isNothing g) || ((prec delta) (fst . fromJust $ g) (getProps q) == Just Yield) = do
              newStates <- wrapStates (sIdGen globals) $ popFirst ((deltaPush delta) (getState q) (getProps q))
              foldM (reachPush isDestState isDestStack globals delta q g) False newStates
          | ((prec delta) (fst . fromJust $ g) (getProps q) == Just Equal) = do
              newStates <- wrapStates (sIdGen globals) $ popFirst ((deltaShift delta) (getState q) (getProps q))
              let reachShift acc p
                    = if acc
                      then return True
                      else debug ("Shift: q = " ++ show q ++ "\ng = " ++ show g ++ "\n") $
                           reach isDestState isDestStack globals delta p (Just (getProps q, (snd . fromJust $ g)))
              foldM reachShift False newStates
          | ((prec delta) (fst . fromJust $ g) (getProps q) == Just Take) = do
              newStates <- wrapStates (sIdGen globals) $ popFirst ((deltaPop delta) (getState q) (getState . snd . fromJust $ g))
              foldM (reachPop isDestState isDestStack globals delta q g) False newStates
          | otherwise = return False
    cases

reachPush :: (Eq a, Ord a, Hashable a, Show a)
          => (StateId a -> Bool)
          -> (Stack a -> Bool)
          -> Globals s a
          -> Delta a
          -> StateId a
          -> Stack a
          -> Bool
          -> StateId a
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

reachPop :: (Eq a, Ord a, Hashable a, Show a)
         => (StateId a -> Bool)
         -> (Stack a -> Bool)
         -> Globals s a
         -> Delta a
         -> StateId a
         -> Stack a
         -> Bool
         -> StateId a
         -> ST s Bool
reachPop _ _ _ _ _ _ True _ = return True
reachPop isDestState isDestStack globals delta q g False p = do
  insertSM (suppEnds globals) (snd . fromJust $ g) p
  currentSuppStarts <- lookupSM (suppStarts globals) (snd . fromJust $ g)
  foldM (\acc g' -> if acc
                    then return True
                    else debug ("Pop: q = " ++ show q ++ "\ng = " ++ show g ++ "\n") $
                         reach isDestState isDestStack globals delta p g')
    False
    (Set.filter (\g' -> isNothing g' ||
                        ((prec delta) (fst . fromJust $ g') (getProps (snd . fromJust $ g))) == Just Yield)
      currentSuppStarts)


isEmpty :: (Ord a, Eq a, Hashable a, Show a)
        => Delta a
        -> [State a]
        -> (State a -> Bool)
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

isSatisfiable :: (Checkable f, Ord a, Hashable a, Eq a, Show a)
              => f a
              -> ([Prop a], [Prop a])
              -> PrecFunc a
              -> Bool
isSatisfiable phi ap precf =
  let (initials, isFinal, dPush, dShift, dPop) = makeOpa phi ap precf
      delta = Delta { prec = precf,
                      deltaPush = dPush,
                      deltaShift = dShift,
                      deltaPop = dPop }
  in not $ isEmpty delta initials isFinal

isSatisfiablePotlV2 :: (Ord a)
                    => P2.Formula a
                    -> ([Prop a], [Prop a])
                    -> [StructPrecRel a]
                    -> Bool
isSatisfiablePotlV2 phi ap precf =
  let (tphi, tap, tprecr) = toIntAP phi ap precf
  in isSatisfiable tphi tap (fromStructPR tprecr)

toIntAP :: (Ord a)
        => P2.Formula a
        -> ([Prop a], [Prop a])
        -> [StructPrecRel a]
        -> (P2.Formula Int, ([Prop Int], [Prop Int]), [StructPrecRel Int])
toIntAP phi (sls, als) precr =
  let phiAP = [p | Atomic p <- Set.toList (closure (toReducedPotl phi) [])] -- TODO make Formula Foldable
      relAP = concatMap (\(sl1, sl2, _) -> [sl1, sl2]) precr
      allProps = map (\(Prop p) -> p) (filter (\p -> p /= End) $ nub $ sls ++ als ++ phiAP ++ relAP)
      apMap = Map.fromList $ zip allProps [1..]
      trans p = fromJust $ Map.lookup p apMap
  in (fmap trans phi
     , (map (fmap trans) sls, map (fmap trans) als)
     , map (\(sl1, sl2, pr) -> ( fmap trans $ sl1
                               , fmap trans $ sl2
                               , pr
                               )
           ) precr
     )

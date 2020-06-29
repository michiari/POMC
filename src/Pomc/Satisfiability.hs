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
import Pomc.Prec (Prec(..), PrecRel, PrecFunc, fromRelations)
import Pomc.Check (Checkable(..), Atom(..), State(..), makeOpa, closure)
import Pomc.RPotl (Formula(Atomic), atomic)
import qualified Pomc.PotlV2 as P2

import Control.Monad (foldM)
import Control.Monad.ST (ST)
import qualified Control.Monad.ST as ST

import Data.Maybe
import Data.List (nub, partition)

import Data.Set (Set)
import qualified Data.Set as Set

import qualified Data.Map as Map

import Data.Hashable
import qualified Data.HashTable.ST.Basic as BH
import qualified Data.HashTable.Class as H

--import Debug.Trace (trace)

debug :: String -> a -> a
--debug = trace
debug _ x = x

type HashTable s k v = BH.HashTable s k v

memberHT :: (Eq k, Hashable k) => HashTable s k v -> k -> ST.ST s Bool
memberHT ht key = do
  val <- H.lookup ht key
  return $ isJust val

-- Map to lists
-- TODO map to sets
type ListMap s k v = HashTable s k [v]

insertLM :: (Eq k, Hashable k) => ListMap s k v -> k -> v -> ST.ST s ()
insertLM lm key val = H.mutate lm key consVal
  where consVal Nothing = (Just [val], ())
        consVal (Just vals) = (Just (val:vals), ())

lookupLM :: (Eq k, Hashable k) => ListMap s k v -> k -> ST.ST s [v]
lookupLM lm key = do
  val <- H.lookup lm key
  return $ maybeList val
    where maybeList Nothing = []
          maybeList (Just l) = l

emptyLM :: ST.ST s (ListMap s k v)
emptyLM = H.new


-- Input symbol
type Input a = Set (Prop a)

-- Stack symbol
type Stack a = Maybe (Input a, State a)

data Globals s a = Globals { visited :: HashTable s (State a, Stack a) (),
                             suppStarts :: ListMap s (State a) (Stack a),
                             suppEnds :: ListMap s (State a) (State a) }
data Delta a = Delta { prec :: (Input a -> Input a -> Maybe Prec),
                       deltaPush :: State a -> Input a -> [State a],
                       deltaShift :: State a -> Input a -> [State a],
                       deltaPop :: State a -> State a -> [State a] }

getProps :: (Ord a, Hashable a) => State a -> Input a
getProps s = Set.map (\(Atomic p) -> p) $ Set.filter atomic (atomFormulaSet . current $ s)

popFirst prec stackProps states = let (popStates, others) = partition (\s -> prec stackProps (getProps s) == Just Take) states
                                  in popStates ++ others

reach :: (Ord a, Eq a, Hashable a, Show a)
      => (State a -> Bool)
      -> (Stack a -> Bool)
      -> Globals s a
      -> Delta a
      -> State a
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
          | (isNothing g) || ((prec delta) (fst . fromJust $ g) (getProps q) == Just Yield)
              = foldM (reachPush isDestState isDestStack globals delta q g) False (popFirst (prec delta) (getProps q) $ (deltaPush delta) q (getProps q))
          | ((prec delta) (fst . fromJust $ g) (getProps q) == Just Equal)
              = foldM (\acc p -> if acc
                                 then debug ("Shift: q = " ++ show q ++ "\ng = " ++ show g ++ "\n") $ return True
                                 else reach isDestState isDestStack globals delta p (Just (getProps q, (snd . fromJust $ g))))
                False
                (popFirst (prec delta) (fst . fromJust $ g) $ (deltaShift delta) q (getProps q))
          | ((prec delta) (fst . fromJust $ g) (getProps q) == Just Take)
              = foldM (reachPop isDestState isDestStack globals delta q g) False ((deltaPop delta) q (snd . fromJust $ g))
          | otherwise = return False
    cases

reachPush :: (Eq a, Ord a, Hashable a, Show a)
          => (State a -> Bool)
          -> (Stack a -> Bool)
          -> Globals s a
          -> Delta a
          -> State a
          -> Stack a
          -> Bool
          -> State a
          -> ST s Bool
reachPush _ _ _ _ _ _ True _ = return True
reachPush isDestState isDestStack globals delta q g False p = do
  insertLM (suppStarts globals) q g
  alreadyVisited <- memberHT (visited globals) (p, Just (getProps q, p))
  if not alreadyVisited
    then do
    res <- reach isDestState isDestStack globals delta p (Just (getProps q, q))
    if res
      then debug ("Push: q = " ++ show q ++ "\ng = " ++ show g ++ "\n") $ return True
      else return False
    else do
    currentSuppEnds <- lookupLM (suppEnds globals) q
    foldM (\acc s -> if acc
                     then debug ("Push (summary): q = " ++ show q ++ "\ng = " ++ show g ++ "\n") $ return True
                     else reach isDestState isDestStack globals delta s g)
      False
      currentSuppEnds

reachPop :: (Eq a, Ord a, Hashable a, Show a)
         => (State a -> Bool)
         -> (Stack a -> Bool)
         -> Globals s a
         -> Delta a
         -> State a
         -> Stack a
         -> Bool
         -> State a
         -> ST s Bool
reachPop _ _ _ _ _ _ True _ = return True
reachPop isDestState isDestStack globals delta q g False p = do
  insertLM (suppEnds globals) (snd . fromJust $ g) p
  currentSuppStarts <- lookupLM (suppStarts globals) (snd . fromJust $ g)
  foldM (\acc g' -> if acc
                    then debug ("Pop: q = " ++ show q ++ "\ng = " ++ show g ++ "\n") $  return True
                    else reach isDestState isDestStack globals delta p g')
    False
    (filter (\g' -> isNothing g' ||
                    ((prec delta) (fst . fromJust $ g') (getProps (snd . fromJust $ g))) == Just Yield)
      currentSuppStarts)


isEmpty :: (Ord a, Eq a, Hashable a, Show a)
        => Delta a
        -> [State a]
        -> (State a -> Bool)
        -> Bool
isEmpty delta initials isFinal = not $
  ST.runST (do
               emptyVisited <- H.new
               emptySuppStarts <- emptyLM
               emptySuppEnds <- emptyLM
               let globals = Globals { visited = emptyVisited,
                                       suppStarts = emptySuppStarts,
                                       suppEnds = emptySuppEnds }
                 in foldM (\acc q -> if acc
                            then return True
                            else (reach isFinal isNothing globals delta q Nothing))
                    False
                    initials)

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
                    -> [PrecRel a]
                    -> Bool
isSatisfiablePotlV2 phi ap precf =
  let (tphi, tap, tprecr) = toIntAP phi ap precf
  in isSatisfiable tphi tap (fromRelations tprecr)

toIntAP :: (Ord a)
        => P2.Formula a
        -> ([Prop a], [Prop a])
        -> [PrecRel a]
        -> (P2.Formula Int, ([Prop Int], [Prop Int]), [PrecRel Int])
toIntAP phi (sls, als) precr =
  let phiAP = [p | Atomic p <- Set.toList (closure (toReducedPotl phi) [])] -- TODO make Formula Foldable
      relAP = concatMap (\(s1, s2, _) -> Set.toList $ Set.union s1 s2) precr
      allProps = map (\(Prop p) -> p) (filter (\p -> p /= End) $ nub $ sls ++ als ++ phiAP ++ relAP)
      apMap = Map.fromList $ zip allProps [1..]
      trans p = fromJust $ Map.lookup p apMap
  in (fmap trans phi
     , (map (fmap trans) sls, map (fmap trans) als)
     , map (\(s1, s2, pr) -> ( Set.map (fmap trans) s1
                             , Set.map (fmap trans) s2
                             , pr
                             )
           ) precr
     )

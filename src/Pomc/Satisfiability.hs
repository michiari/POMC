{- |
   Module      : Pomc.Satisfiability
   Copyright   : 2020 Michele Chiari
   License     : MIT
   Maintainer  : Michele Chiari
-}

module Pomc.Satisfiability (
                             isSatisfiable
                           , Input(..)
                           ) where

import Pomc.Prop (Prop(..))
import Pomc.Prec (Prec(..))
import Pomc.Check (Checkable(..), Atom(..), State(..), makeOpa)
import Pomc.RPotl (Formula(Atomic), atomic)
import Pomc.Util (notMember)
import qualified Control.Monad.State.Strict as St
import Control.Monad (foldM)
import Data.Maybe

import Data.HashSet (HashSet)
import qualified Data.HashSet as Set

import Data.Hashable

import Data.Map.Strict (Map(..))
import qualified Data.Map.Strict as HM

import Debug.Trace (trace)

-- Map to lists
type ListMap k v = Map k [v]

insertLM :: (Eq k, Ord k) => k -> v -> ListMap k v -> ListMap k v
insertLM key val lm = HM.alter consVal key lm
  where consVal Nothing = Just [val]
        consVal (Just vals) = Just (val:vals)

lookupLM :: (Eq k, Ord k) => k -> ListMap k v -> [v]
lookupLM key lm = HM.findWithDefault [] key lm

emptyLM :: ListMap k v
emptyLM = HM.empty


-- Input symbol
type Input a = HashSet (Prop a)

-- Stack symbol
type Stack a = Maybe (Input a, State a)

data Globals a = Globals { visited :: HashSet (State a, Stack a),
                           suppStarts :: ListMap (State a) (Stack a),
                           suppEnds :: ListMap (State a) (State a) }
data Delta a = Delta { prec :: (Input a -> Input a -> Maybe Prec),
                       deltaPush :: State a -> Input a -> [State a],
                       deltaShift :: State a -> Input a -> [State a],
                       deltaPop :: State a -> State a -> [State a] }

getProps :: (Ord a, Hashable a) => State a -> Input a
getProps s = Set.map (\(Atomic p) -> p) $ Set.filter atomic (atomFormulaSet . current $ s)

reach :: (Ord a, Eq a, Hashable a, Show a)
      => (State a -> Bool)
      -> (Stack a -> Bool)
      -> Delta a
      -> State a
      -> Stack a
      -> St.State (Globals a) Bool
reach isDestState isDestStack delta q g = do
  globals <- St.get
  if ({-# SCC "reach:setMember" #-} Set.member (q, g)) $ visited globals
    then return False
    else do
    St.put $ Globals { visited = Set.insert (q, g) (visited globals),
                       suppStarts = suppStarts globals,
                       suppEnds = suppEnds globals }
    let cases
          | (isDestState q) && (isDestStack g) = return True
          | (isNothing g) || ((prec delta) (fst . fromJust $ g) (getProps q) == Just Yield)
              = foldM (reachPush isDestState isDestStack delta q g) False ((deltaPush delta) q (getProps q))
          | ((prec delta) (fst . fromJust $ g) (getProps q) == Just Equal)
              = foldM (\acc p -> if acc
                                 then return True
                                 else reach isDestState isDestStack delta p (Just (getProps q, (snd . fromJust $ g))))
                False
                ((deltaShift delta) q (getProps q))
          | ((prec delta) (fst . fromJust $ g) (getProps q) == Just Take)
              = foldM (reachPop isDestState isDestStack delta q g) False ((deltaPop delta) q (snd . fromJust $ g))
          | otherwise = return False
    cases

reachPush :: (Eq a, Ord a, Hashable a, Show a)
          => (State a -> Bool)
          -> (Stack a -> Bool)
          -> Delta a
          -> State a
          -> Stack a
          -> Bool
          -> State a
          -> St.State (Globals a) Bool
reachPush _ _ _ _ _ True _ = return True
reachPush isDestState isDestStack delta q g False p = do
  globals <- St.get
  St.put $ Globals { visited = visited globals,
                     suppStarts = insertLM q g (suppStarts globals),
                     suppEnds = suppEnds globals }
  if notMember (p, Just (getProps q, p)) (visited globals)
    then reach isDestState isDestStack delta p (Just (getProps q, q))
    else foldM (\acc s -> if acc
                          then return True
                          else reach isDestState isDestStack delta s g)
               False
               (lookupLM q (suppEnds globals))

reachPop :: (Eq a, Ord a, Hashable a, Show a)
         => (State a -> Bool)
         -> (Stack a -> Bool)
         -> Delta a
         -> State a
         -> Stack a
         -> Bool
         -> State a
         -> St.State (Globals a) Bool
reachPop _ _ _ _ _ True _ = return True
reachPop isDestState isDestStack delta q g False p = do
  globals <- St.get
  St.put $ Globals { visited = visited globals,
                     suppStarts = suppStarts globals,
                     suppEnds = {-# SCC "reachPop:insertLM" #-} insertLM (snd . fromJust $ g) p (suppEnds globals) }
  foldM (\acc g' -> if acc
                    then {-# SCC "reachPop:retTrue" #-} return True
                    else {-# SCC "reachPop:recurse" #-} reach isDestState isDestStack delta p g')
    False
    (filter (\g' -> isNothing g' ||
                    ((prec delta) (fst . fromJust $ g') (getProps q)) == Just Yield)
      ({-# SCC "reachPop:lookupLM" #-} (lookupLM (snd . fromJust $ g) (suppStarts globals))))


isEmpty :: (Ord a, Eq a, Hashable a, Show a)
        => Delta a
        -> [State a]
        -> (State a -> Bool)
        -> Bool
isEmpty delta initials isFinal = not $
  St.evalState
    (foldM (\acc q -> if acc
                      then return True
                      else (reach isFinal isNothing delta q Nothing))
     False
     initials)
    (Globals { visited = Set.empty,
               suppStarts = emptyLM,
               suppEnds = emptyLM })

isSatisfiable :: (Checkable f, Ord a, Hashable a, Eq a, Show a)
              => f a
              -> ([Prop a], [Prop a])
              -> (Input a -> Input a -> Maybe Prec)
              -> Bool
isSatisfiable phi ap precf =
  let (initials, isFinal, dPush, dShift, dPop) = makeOpa phi ap precf
      delta = Delta { prec = precf,
                      deltaPush = dPush,
                      deltaShift = dShift,
                      deltaPop = dPop }
  in not $ isEmpty delta initials isFinal


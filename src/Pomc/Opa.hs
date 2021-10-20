{-# LANGUAGE DeriveGeneric, DeriveAnyClass #-}

{- |
   Module      : Pomc.Opa
   Copyright   : 2020-2021 Davide Bergamaschi and Michele Chiari
   License     : MIT
   Maintainer  : Michele Chiari
-}

module Pomc.Opa ( -- * Run functions
                  run
                , augRun
                , parAugRun
                  -- * OPA type and relative utilities
                , Opa(..)
                , runOpa
                ) where

import Pomc.Prec (Prec(..))
import Pomc.Util (any', safeHead, safeTail, parMap)

import Control.Parallel.Strategies(NFData)
import GHC.Generics (Generic)

data Opa s t = Opa
    { alphabet   :: [t]
    , prec       :: t -> t -> Maybe Prec
    , states     :: [s]
    , initials   :: [s]
    , finals     :: [s]
    , deltaShift :: s -> t -> [s]
    , deltaPush  :: s -> t -> [s]
    , deltaPop   :: s -> s -> [s]
    }

-- a configuration of a opa
data Config s t = Config
    { confState :: s
    , confStack :: [(t, s)]
    , confInput :: [t]
    } deriving (Show, Generic, NFData)

runOpa :: (Eq s) => Opa s t -> [t] -> Bool
runOpa (Opa _ precf _ ini fin dshift dpush dpop) tokens =
  run precf ini (`elem` fin) dshift dpush dpop tokens

-- run some tokens over an OPA and check acceptance
run :: (t -> t -> Maybe Prec) -- precedence relation
    -> [s] -- list of initial states
    -> (s -> Bool) -- is a state final?
    -> (s -> t -> [s]) -- deltaShift (non deterministic)
    -> (s -> t -> [s]) -- deltaPush
    -> (s -> s -> [s]) -- deltaPop
    -> [t] -- input tokens
    -> Bool --is the string accepted?
run precf ini isFinal dShift dPush dPop tokens =
  any'
    (run' precf dShift dPush dPop isFinal)
    (map (\i -> Config i [] tokens) ini)
  where
    run' precf' dshift dpush dpop isFinal' conf@(Config s stack tokens')
      -- No more input and empty stack: accept / reject
      | null tokens' && null stack = isFinal' s

      -- No more input but stack non-empty: pop
      | null tokens' = recurse (pop dpop conf)

      -- Stack empty: push
      | null stack = recurse (push dpush conf)

      -- Evaluate stack top precedence w.r.t. next token
      | otherwise = case precf' (fst top) t of
                      -- Undefined precedence relation: reject
                      Nothing    -> False
                      -- Stack top yields to next token: push
                      Just Yield -> recurse (push dpush conf)
                      -- Stack top has same precedence as next token: shift
                      Just Equal -> recurse (shift dshift conf)
                      -- Stack top takes precedence on next token: pop
                      Just Take  -> recurse (pop dpop conf)
      where top = head stack  --
            t   = head tokens' -- safe due to laziness
            recurse = any' (run' precf' dshift dpush dpop isFinal')

-- run some tokens over an OPA and check acceptance, but use the lookahead for early discard of non accepting computations
augRun :: (t -> t -> Maybe Prec)
       -> [s]
       -> (s -> Bool)
       -> (Maybe t -> s -> t -> [s])
       -> (Maybe t -> s -> t -> [s])
       -> (Maybe t -> s -> s -> [s])
       -> [t]
       -> Bool
augRun precf ini isFinal augDeltaShift augDeltaPush augDeltaPop tokens =
  let ics = (map (\i -> Config i [] tokens) ini)
  in any' (run' precf augDeltaShift augDeltaPush augDeltaPop isFinal) ics
  where
    run' precf' adshift adpush adpop isFinal' conf@(Config s stack tokens')
      -- No more input and empty stack: accept / reject
      | null tokens' && null stack = isFinal' s

      -- No more input but stack non-empty: pop
      | null tokens' = recurse (pop dpop conf)

      -- Stack empty: push
      | null stack = recurse (push dpush conf)

      -- Evaluate stack top precedence w.r.t. next token
      | otherwise = case precf' (fst top) t of
                      -- Undefined precedence relation: reject
                      Nothing    -> False
                      -- Stack top yields to next token: push
                      Just Yield -> recurse (push dpush conf)
                      -- Stack top has same precedence as next token: shift
                      Just Equal -> recurse (shift dshift conf)
                      -- Stack top takes precedence on next token: pop
                      Just Take  -> recurse (pop dpop conf)
      where lookahead = safeTail tokens' >>= safeHead
            dshift = adshift lookahead
            dpush  = adpush  lookahead
            dpop   = adpop   lookahead
            top = head stack  --
            t   = head tokens' -- safe due to laziness
            recurse = any' (run' precf' adshift adpush adpop isFinal')


-- same as AugRun, but with some parallelim
parAugRun :: (NFData s, NFData t)
          => (t -> t -> Maybe Prec)
          -> [s]
          -> (s -> Bool)
          -> (Maybe t -> s -> t -> [s])
          -> (Maybe t -> s -> t -> [s])
          -> (Maybe t -> s -> s -> [s])
          -> [t]
          -> Bool
parAugRun precf ini isFinal augDeltaShift augDeltaPush augDeltaPop tokens =
  let ics = (map (\i -> Config i [] tokens) ini)
      results = parMap (run' precf augDeltaShift augDeltaPush augDeltaPop isFinal) ics
  in any id results
  where
    run' precf' adshift adpush adpop isFinal' conf@(Config s stack tokens')
      -- No more input and empty stack: accept / reject
      | null tokens' && null stack = isFinal' s

      -- No more input but stack non-empty: pop
      | null tokens' = recurse (pop dpop conf)

      -- Stack empty: push
      | null stack = recurse (push dpush conf)

      -- Evaluate stack top precedence w.r.t. next token
      | otherwise = case precf' (fst top) t of
                      -- Undefined precedence relation: reject
                      Nothing    -> False
                      -- Stack top yields to next token: push
                      Just Yield -> recurse (push dpush conf)
                      -- Stack top has same precedence as next token: shift
                      Just Equal -> recurse (shift dshift conf)
                      -- Stack top takes precedence on next token: pop
                      Just Take  -> recurse (pop dpop conf)
      where lookahead = safeTail tokens' >>= safeHead
            dshift = adshift lookahead
            dpush  = adpush  lookahead
            dpop   = adpop   lookahead
            top = head stack  --
            t   = head tokens' -- safe due to laziness
            recurse = any id . parMap (run' precf' adshift adpush adpop isFinal')

-- Partial: assumes token list not empty
push :: (s -> t -> [s]) -> Config s t -> [Config s t]
push dpush (Config s stack (t:ts)) =
  map (\s' -> (Config s' ((t, s):stack) ts))
      (dpush s t)
push _ (Config _ _ []) = error "Trying to push with no more tokens."

-- Partial: assumes token list and stack not empty
shift :: (s -> t -> [s]) -> Config s t -> [Config s t]
shift dshift (Config s stack (t:ts)) =
  map (\s' -> (Config s' ((t, (snd (head stack))):(tail stack)) ts))
      (dshift s t)
shift _ (Config _ _ []) = error "Trying to shift with no more tokens."

-- Partial: assumes stack not empty
pop :: (s -> s -> [s]) -> Config s t -> [Config s t]
pop dpop (Config s stack tokens) =
  map (\s' -> (Config s' (tail stack) tokens))
      (dpop s (snd (head stack)))

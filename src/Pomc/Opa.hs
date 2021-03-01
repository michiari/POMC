{-# LANGUAGE DeriveGeneric, DeriveAnyClass #-}

{- |
   Module      : Pomc.Opa
   Copyright   : 2020 Davide Bergamaschi
   License     : MIT
   Maintainer  : Davide Bergamaschi
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

import Control.Parallel.Strategies(NFData(..))
import GHC.Generics (Generic)
import qualified Data.Vector as V

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
runOpa (Opa _ prec _ initials finals dshift dpush dpop) tokens =
  run prec initials (`elem` finals) dshift dpush dpop tokens

-- run some tokens over an OPA and check acceptance
run :: (t -> t -> Maybe Prec) -- precedence relation
    -> [s] -- list of initial states
    -> (s -> Bool) -- is a state final?
    -> (s -> t -> [s]) -- deltaShift (non deterministic)
    -> (s -> t -> [s]) -- deltaPush
    -> (s -> s -> [s]) -- deltaPop
    -> [t] -- input tokens
    -> Bool --is the string accepted?
run prec initials isFinal deltaShift deltaPush deltaPop tokens =
  any'
    (run' prec deltaShift deltaPush deltaPop isFinal)
    (map (\i -> Config i [] tokens) initials)
  where
    run' prec dshift dpush dpop isFinal conf@(Config s stack tokens)
      -- No more input and empty stack: accept / reject
      | null tokens && null stack = isFinal s

      -- No more input but stack non-empty: pop
      | null tokens = recurse (pop dpop conf)

      -- Stack empty: push
      | null stack = recurse (push dpush conf)

      -- Evaluate stack top precedence w.r.t. next token
      | otherwise = case prec (fst top) t of
                      -- Undefined precedence relation: reject
                      Nothing    -> False
                      -- Stack top yields to next token: push
                      Just Yield -> recurse (push dpush conf)
                      -- Stack top has same precedence as next token: shift
                      Just Equal -> recurse (shift dshift conf)
                      -- Stack top takes precedence on next token: pop
                      Just Take  -> recurse (pop dpop conf)
      where top = head stack  --
            t   = head tokens -- safe due to laziness
            recurse = any' (run' prec dshift dpush dpop isFinal)

augRun :: (t -> t -> Maybe Prec)
       -> [s]
       -> (s -> Bool)
       -> (Maybe t -> s -> t -> [s])
       -> (Maybe t -> s -> t -> [s])
       -> (Maybe t -> s -> s -> [s])
       -> [t]
       -> Bool
augRun prec initials isFinal augDeltaShift augDeltaPush augDeltaPop tokens =
  let ics = (map (\i -> Config i [] tokens) initials)
  in any' (run' prec augDeltaShift augDeltaPush augDeltaPop isFinal) ics
  where
    run' prec adshift adpush adpop isFinal conf@(Config s stack tokens)
      -- No more input and empty stack: accept / reject
      | null tokens && null stack = isFinal s

      -- No more input but stack non-empty: pop
      | null tokens = recurse (pop dpop conf)

      -- Stack empty: push
      | null stack = recurse (push dpush conf)

      -- Evaluate stack top precedence w.r.t. next token
      | otherwise = case prec (fst top) t of
                      -- Undefined precedence relation: reject
                      Nothing    -> False
                      -- Stack top yields to next token: push
                      Just Yield -> recurse (push dpush conf)
                      -- Stack top has same precedence as next token: shift
                      Just Equal -> recurse (shift dshift conf)
                      -- Stack top takes precedence on next token: pop
                      Just Take  -> recurse (pop dpop conf)
      where lookahead = safeTail tokens >>= safeHead
            dshift = adshift lookahead
            dpush  = adpush  lookahead
            dpop   = adpop   lookahead
            top = head stack  --
            t   = head tokens -- safe due to laziness
            recurse = any' (run' prec adshift adpush adpop isFinal)


interChunks nchunks xs = interChunks' (V.generate nchunks (const [])) 0 xs
  where interChunks' vec _ [] = vec
        interChunks' vec i (x:xs) = interChunks'
                                      (vec V.// [(i,x:(vec V.! i))])
                                      ((i + 1) `mod` nchunks)
                                      xs

parAugRun :: (NFData s, NFData t)
          => (t -> t -> Maybe Prec)
          -> [s]
          -> (s -> Bool)
          -> (Maybe t -> s -> t -> [s])
          -> (Maybe t -> s -> t -> [s])
          -> (Maybe t -> s -> s -> [s])
          -> [t]
          -> Bool
parAugRun prec initials isFinal augDeltaShift augDeltaPush augDeltaPop tokens =
  let ics = (map (\i -> Config i [] tokens) initials)
      results = parMap (run' prec augDeltaShift augDeltaPush augDeltaPop isFinal) ics              
  in not $ null $ filter (== True) results
  where
    run' prec adshift adpush adpop isFinal conf@(Config s stack tokens)
      -- No more input and empty stack: accept / reject
      | null tokens && null stack = isFinal s

      -- No more input but stack non-empty: pop
      | null tokens = recurse (pop dpop conf)

      -- Stack empty: push
      | null stack = recurse (push dpush conf)

      -- Evaluate stack top precedence w.r.t. next token
      | otherwise = case prec (fst top) t of
                      -- Undefined precedence relation: reject
                      Nothing    -> False
                      -- Stack top yields to next token: push
                      Just Yield -> recurse (push dpush conf) 
                      -- Stack top has same precedence as next token: shift
                      Just Equal -> recurse (shift dshift conf) 
                      -- Stack top takes precedence on next token: pop
                      Just Take  -> recurse (pop dpop conf) 
      where lookahead = safeTail tokens >>= safeHead
            dshift = adshift lookahead
            dpush  = adpush  lookahead
            dpop   = adpop   lookahead
            top = head stack  --
            t   = head tokens -- safe due to laziness
            recurse xs = not $ null $ filter (== True) $ parMap (run' prec augDeltaShift augDeltaPush augDeltaPop isFinal) xs
            

-- Partial: assumes token list not empty
push :: (s -> t -> [s]) -> Config s t -> [Config s t]
push dpush (Config s stack (t:ts)) =
  map (\s' -> (Config s' ((t, s):stack) ts))
      (dpush s t)

-- Partial: assumes token list and stack not empty
shift :: (s -> t -> [s]) -> Config s t -> [Config s t]
shift dshift (Config s stack (t:ts)) =
  map (\s' -> (Config s' ((t, (snd (head stack))):(tail stack)) ts))
      (dshift s t)

-- Partial: assumes stack not empty
pop :: (s -> s -> [s]) -> Config s t -> [Config s t]
pop dpop (Config s stack tokens) =
  map (\s' -> (Config s' (tail stack) tokens))
      (dpop s (snd (head stack)))

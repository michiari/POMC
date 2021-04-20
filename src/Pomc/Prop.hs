{-# LANGUAGE DeriveGeneric #-}

{- |
   Module      : Pomc.Prop
   Copyright   : 2020-2021 Davide Bergamaschi, Michele Chiari
   License     : MIT
   Maintainer  : Michele Chiari
-}

module Pomc.Prop ( -- * Atomic proposition type
                   Prop(..)
                 ) where

import GHC.Generics (Generic)

import Data.Hashable

data Prop a = Prop !a | End deriving (Eq, Ord, Show, Generic)

instance Hashable a => Hashable (Prop a)

instance Functor Prop where
  fmap f (Prop a) = Prop (f a)
  fmap _ End = End

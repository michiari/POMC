{-# LANGUAGE DeriveGeneric, DeriveAnyClass #-}

{- |
   Module      : Pomc.Prop
   Copyright   : 2020 Davide Bergamaschi
   License     : MIT
   Maintainer  : Davide Bergamaschi
-}

module Pomc.Prop ( -- * Atomic proposition type
                   Prop(..)
                 ) where

import Control.DeepSeq (NFData)
import GHC.Generics (Generic)
import Data.Hashable

data Prop a = Prop a | End deriving (Eq, Ord, Show, Generic, NFData)

instance Hashable a => Hashable (Prop a)

instance Functor Prop where
  fmap f (Prop a) = Prop (f a)
  fmap _ End = End

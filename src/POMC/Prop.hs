{-# LANGUAGE DeriveGeneric, DeriveAnyClass #-}

module POMC.Prop (Prop(..)) where

import Control.DeepSeq (NFData)
import GHC.Generics (Generic)

data Prop a = Prop a | End deriving (Eq, Ord, Show, Generic, NFData)

instance Functor Prop where
  fmap f (Prop a) = Prop (f a)
  fmap _ End = End
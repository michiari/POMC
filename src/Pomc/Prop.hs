{-# LANGUAGE DeriveGeneric #-}

{- |
   Module      : Pomc.Prop
   Copyright   : 2020-2024 Davide Bergamaschi, Michele Chiari
   License     : MIT
   Maintainer  : Michele Chiari
-}

module Pomc.Prop ( Prop(..)
                 , unprop
                 , notEnd
                 ) where

import GHC.Generics (Generic)

import Data.Hashable

data Prop a = Prop !a | End deriving (Eq, Ord, Show, Generic)

instance Hashable a => Hashable (Prop a)

instance Functor Prop where
  fmap f (Prop a) = Prop (f a)
  fmap _ End = End

unprop :: Prop a -> a
unprop (Prop p) = p
unprop End = error "Cannot unprop End."

notEnd :: Prop a -> Bool
notEnd End = False
notEnd _ = True

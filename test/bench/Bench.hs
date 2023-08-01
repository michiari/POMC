{- |
   Module      : Bench
   Copyright   : 2021-23 Michele Chiari
   License     : MIT
   Maintainer  : Michele Chiari
-}

import Test.Tasty.Bench

import qualified Pomc.Test.TestSat (benchs)

main :: IO ()
main = defaultMain [Pomc.Test.TestSat.benchs]

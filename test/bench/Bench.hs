{- |
   Module      : Bench
   Copyright   : 2021-24 Michele Chiari
   License     : MIT
   Maintainer  : Michele Chiari
-}

import Test.Tasty.Bench

import qualified Pomc.Test.TestSat   (benchs)
import qualified Pomc.Test.TestMP    (benchs)
import qualified Pomc.Test.TestZ3Sat (benchs)
import qualified Pomc.Test.TestZ3MC  (benchs)

main :: IO ()
main = defaultMain [ Pomc.Test.TestSat.benchs
                   , Pomc.Test.TestMP.benchs
                   , Pomc.Test.TestZ3Sat.benchs
                   , Pomc.Test.TestZ3MC.benchs
                   ]

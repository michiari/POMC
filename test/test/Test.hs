{- |
   Module      : Test
   Copyright   : 2021-23 Michele Chiari
   License     : MIT
   Maintainer  : Michele Chiari
-}

import Test.Tasty

import qualified Pomc.Test.TestOpa      (tests)
import qualified Pomc.Test.TestCheck    (tests)
import qualified Pomc.Test.TestSat      (tests, slowTests)
import qualified Pomc.Test.TestMC       (tests, slowTests)
import qualified Pomc.Test.TestMP       (tests)
import qualified Pomc.Test.TestSatOmega (tests, slowTests)
import qualified Pomc.Test.TestMCOmega  (tests, slowTests)
import qualified Pomc.Test.TestProbTermination (tests)

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Tests" [normalTests, slowTests]

normalTests :: TestTree
normalTests = testGroup "Normal Tests"
  [ Pomc.Test.TestOpa.tests
  , Pomc.Test.TestCheck.tests
  , Pomc.Test.TestSat.tests
  , Pomc.Test.TestMC.tests
  , Pomc.Test.TestMP.tests
  , Pomc.Test.TestSatOmega.tests
  , Pomc.Test.TestMCOmega.tests
  , Pomc.Test.TestProbTermination.tests
  ]

slowTests :: TestTree
slowTests = testGroup "Slow Tests"
  [ Pomc.Test.TestSat.slowTests
  , Pomc.Test.TestMC.slowTests
  , Pomc.Test.TestSatOmega.slowTests
  , Pomc.Test.TestMCOmega.slowTests
  ]

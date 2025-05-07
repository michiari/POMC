{- |
   Module      : Test
   Copyright   : 2021-2024 Michele Chiari
   License     : MIT
   Maintainer  : Michele Chiari
-}

import Test.Tasty

import qualified Pomc.Test.TestOpa             (tests)
import qualified Pomc.Test.TestCheck           (tests)
import qualified Pomc.Test.TestSat             (tests, slowTests)
import qualified Pomc.Test.TestMC              (tests, slowTests)
import qualified Pomc.Test.TestMP              (tests)
import qualified Pomc.Test.TestSatOmega        (tests, slowTests)
import qualified Pomc.Test.TestMCOmega         (tests, slowTests)
import qualified Pomc.Test.TestZ3Sat           (tests, slowTests)
import qualified Pomc.Test.TestZ3MC            (tests, slowTests)
import qualified Pomc.Test.TestProbTermination (tests)
import qualified Pomc.Test.TestProbQualMC      (tests)
import qualified Pomc.Test.TestProbQuantMC     (tests)
import qualified Pomc.Test.TestMiniProb        (tests)

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
  , Pomc.Test.TestZ3Sat.tests
  , Pomc.Test.TestZ3MC.tests
  , Pomc.Test.TestProbTermination.tests
  , Pomc.Test.TestMiniProb.tests
  , Pomc.Test.TestProbQualMC.tests
  , Pomc.Test.TestProbQuantMC.tests
  ]

slowTests :: TestTree
slowTests = testGroup "Slow Tests"
  [ Pomc.Test.TestSat.slowTests
  , Pomc.Test.TestMC.slowTests
  , Pomc.Test.TestSatOmega.slowTests
  , Pomc.Test.TestMCOmega.slowTests
  , Pomc.Test.TestZ3Sat.slowTests
  , Pomc.Test.TestZ3MC.slowTests
  ]

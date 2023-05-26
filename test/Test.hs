{- |
   Module      : Test
   Copyright   : 2021-23 Michele Chiari
   License     : MIT
   Maintainer  : Michele Chiari
-}

import Test.Tasty

import qualified TestOpa      (tests)
import qualified TestCheck    (tests)
import qualified TestSat      (tests, slowTests)
import qualified TestMC       (tests, slowTests)
import qualified TestMP       (tests)
import qualified TestSatOmega (tests, slowTests)
import qualified TestMCOmega  (tests, slowTests)
import qualified TestZ3Sat    (tests)
import qualified TestZ3MC     (tests)

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Tests" [normalTests, slowTests]

normalTests :: TestTree
normalTests = testGroup "Normal Tests" [ TestOpa.tests
                                       , TestCheck.tests
                                       , TestSat.tests
                                       , TestMC.tests
                                       , TestMP.tests
                                       , TestSatOmega.tests
                                       , TestMCOmega.tests
                                       , TestZ3Sat.tests
                                       , TestZ3MC.tests
                                       ]

slowTests :: TestTree
slowTests = testGroup "Slow Tests" [ TestSat.slowTests
                                   , TestMC.slowTests
                                   , TestSatOmega.slowTests
                                   , TestMCOmega.slowTests
                                   ]

import Test.Tasty

import qualified TestOpa      (tests)
import qualified TestCheck    (tests)
import qualified TestSat      (tests, slowTests)
import qualified TestMC       (tests, slowTests)
import qualified TestMP       (tests)
import qualified TestSatOmega (tests, slowTests)
import qualified TestMCOmega  (tests, slowTests)

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Tests" [normalTests, slowTests]

normalTests :: TestTree
normalTests = testGroup "Normal Tests" [ TestSatOmega.tests
                                       ]

slowTests :: TestTree
slowTests = testGroup "Slow Tests" [ TestSat.slowTests
                                   , TestMC.slowTests
                                   , TestSatOmega.slowTests
                                   , TestMCOmega.slowTests
                                   ]

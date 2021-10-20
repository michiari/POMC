import Test.Tasty

import qualified TestOpa      (tests)
import qualified TestCheck    (tests)
import qualified TestSat      (tests)
import qualified TestMC       (tests)
import qualified TestMP       (tests)
import qualified TestSatOmega (tests)
import qualified TestMCOmega  (tests)

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Tests" [ TestOpa.tests
                          , TestCheck.tests
                          , TestSat.tests
                          , TestMC.tests
                          , TestMP.tests
                          , TestSatOmega.tests
                          , TestMCOmega.tests
                          ]

import Test.Tasty

import qualified TestOpa   (tests)
import qualified TestCheck (tests)
import qualified TestSat   (tests)
import qualified TestMC    (tests)
import qualified TestMP    (tests)

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Tests" [TestOpa.tests, TestCheck.tests, TestSat.tests, TestMC.tests, TestMP.tests]

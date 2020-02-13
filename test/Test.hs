import Test.Tasty

import qualified TestOpa   (tests)
import qualified TestCheck (tests)

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Tests" [TestOpa.tests, TestCheck.tests]

import Test.Tasty

import qualified TestOpa (tests)

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Tests" [TestOpa.tests]

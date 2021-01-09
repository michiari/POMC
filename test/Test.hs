import Test.Tasty

import qualified TestOpa   (tests)
import qualified TestCheck (tests)
import qualified TestSat   (tests)
import qualified TestMC   (tests)

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Tests" [ TestCheck.tests]

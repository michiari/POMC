module TestSMT ( tests ) where

import Pomc.SMTEncoding (isSatisfiable, SMTResult(..))
import Pomc.MiniProc (miniProcAlphabet)
import Pomc.Potl (Formula(..))

import Test.Tasty
import Test.Tasty.HUnit

tests :: TestTree
tests = testGroup "SMTEncoding Tests" [ helloWorld ]

helloWorld :: TestTree
helloWorld = testCase "Hello World"
  $ isSatisfiable T miniProcAlphabet >>= (Sat @=?)

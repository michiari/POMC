{- |
   Module      : TestSat
   Copyright   : 2021-23 Michele Chiari
   License     : MIT
   Maintainer  : Michele Chiari
-}

module TestSat (tests, slowTests) where

import Test.Tasty
import Test.Tasty.HUnit
import Pomc.Satisfiability (isSatisfiableGen)
import OPMs (stlV2Alphabet)
import EvalFormulas (TestCase, zipExpected, excludeIndices, formulas, ap)
import qualified Data.Set as S (toList)

import Pomc.Potl (Formula(..), Dir(..))

tests :: TestTree
tests = testGroup "TestSat.hs Normal Tests"
  $ map makeTestCase
  $ (excludeIndices allTestCases [18, 41, 42] ++ [nestedXNext, xNextNoEqual])

slowTests :: TestTree
slowTests = testGroup "TestSat.hs Slow Tests"
  $ map makeTestCase
  [ allTestCases !! 18
  , allTestCases !! 41
  , allTestCases !! 42
  , andXNext
  ]

makeTestCase :: (TestCase, Bool)
             -> TestTree
makeTestCase ((name, phi), expected) =
  let (sat, trace) = isSatisfiableGen False phi stlV2Alphabet
      debugMsg False _ = "Expected SAT, got UNSAT."
      debugMsg True tr = "Expected UNSAT, got SAT. Trace:\n" ++ show (map S.toList tr)
  in testCase (name ++ " (" ++ show phi ++ ")") $ assertBool (debugMsg sat trace) (sat == expected)

allTestCases :: [(TestCase, Bool)]
allTestCases = zipExpected formulas expectedRes

expectedRes :: [Bool]
expectedRes =
  [ True, True, True, False, False, True
  , True, True, False, True, True, True
  , False, True, True, True, False, True
  , True, True, True, True, True, True -- base_tests
  , True, True, True, True, True -- chain_next
  , True, True, True, True       -- contains_exc
  , True                         -- data_access
  , True, True, True, True       -- empty_frame
  , True                         -- exception_safety
  , True, True, True, True       -- hier_down
  , True                         -- hier_insp
  , True                         -- hier_insp_exc
  , True, True, True, True       -- hier_up
  , True, True                   -- normal_ret
  , True, True                   -- no_throw
  , True, True                   -- stack_inspection
  , True                         -- uninstall_han
  , True, True, True, True       -- until_exc
  , True, True, True             -- until_misc
  ]

nestedXNext :: (TestCase, Bool)
nestedXNext = (("Nested XNexts"
               , XNext Down $ XNext Down $ XNext Down $ XNext Down $ ap "call")
              , True
              )

andXNext :: (TestCase, Bool)
andXNext = (("Conjoined XNexts"
            , XNext Down (ap "call") `And` XNext Up (ap "exc") `And` XNext Down (ap "p") `And` XNext Down (ap "q") `And` XNext Down (ap "w") `And` XNext Down (ap "r"))
           , False
           )

-- This formula being unsatisfiable proves that
-- XBack Down T `And` Not (XBack Up T)
-- is equivalent to XBack <. T on stlV2Alphabet.
xNextNoEqual :: (TestCase, Bool)
xNextNoEqual = (("Right context with yield and take"
              , Eventually (XBack Down T `And` XBack Up T `And` Not ((ap "ret" `And` XBack Down (ap "call")) `Or` (ap "exc" `And` XBack Down (ap "han")))))
             , False
             )

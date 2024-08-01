{- |
   Module      : Pomc.Test.TestSat
   Copyright   : 2021-2024 Michele Chiari
   License     : MIT
   Maintainer  : Michele Chiari
-}

module Pomc.Test.TestSat (tests, slowTests, benchs) where

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.Bench
import Pomc.Satisfiability (isSatisfiableGen)
import Pomc.Test.OPMs (stlV2Alphabet)
import Pomc.Test.EvalFormulas (TestCase, zipExpected, excludeIndices, formulas, ap)
import qualified Data.Set as S (toList)

import Pomc.Potl (Formula(..), Dir(..))

tests :: TestTree
tests = testGroup "TestSat.hs Normal Tests"
  $ map makeTestCase normalTestCases

slowTests :: TestTree
slowTests = testGroup "TestSat.hs Slow Tests"
  $ map makeTestCase slowTestCases

makeTestCase :: (TestCase, Bool) -> TestTree
makeTestCase tce@((_, phi), _) = testCase tname $ tthunk phi
  where (tname, tthunk) = makeTest tce

benchs :: TestTree
benchs = testGroup "TestSat.hs Normal Tests"
  $ map makeBench normalTestCases

makeBench :: (TestCase, Bool) -> Benchmark
makeBench tce@((_, phi), _) = bench bname $ nfAppIO bthunk phi
  where (bname, bthunk) = makeTest tce

makeTest :: (TestCase, Bool) -> (String, Formula String -> Assertion)
makeTest ((name, phi), expected) =
  ( name ++ " (" ++ show phi ++ ")"
  , (\f -> let (sat, trace) = isSatisfiableGen False f stlV2Alphabet
               debugMsg False _ = "Expected SAT, got UNSAT."
               debugMsg True tr = "Expected UNSAT, got SAT. Trace:\n" ++ show (map S.toList tr)
           in assertBool (debugMsg sat trace) (sat == expected))
  )

normalTestCases :: [(TestCase, Bool)]
normalTestCases = excludeIndices allTestCases [18, 41, 42] ++ [nestedXNext, xNextNoEqual]

slowTestCases :: [(TestCase, Bool)]
slowTestCases = [ allTestCases !! 18
                , allTestCases !! 41
                , allTestCases !! 42
                , andXNext
                ]

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

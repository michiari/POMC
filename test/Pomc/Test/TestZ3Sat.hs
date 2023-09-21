{- |
   Module      : Pomc.Test.TestZ3Sat
   Copyright   : 2021-23 Michele Chiari
   License     : MIT
   Maintainer  : Michele Chiari
-}

module Pomc.Test.TestZ3Sat ( tests, slowTests, benchs, isSupported ) where

import Pomc.Test.EvalFormulas (TestCase, zip3Expected, formulas, ap)
import Pomc.Test.OPMs (stlV2Alphabet)
import Pomc.Z3Encoding (isSatisfiable, SMTResult(..), SMTStatus(..))
import Pomc.Potl (Formula(..), Dir(..))

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.Bench
import Data.Word (Word64)

import qualified Debug.Trace as DBG

tests :: TestTree
tests = testGroup "Z3Encoding Satisfiability Tests"
  $ concatMap (map makeTestCase) [efTests, regressionTests]

slowTests :: TestTree
slowTests = testGroup "Z3Encoding Satisfiability Tests" [makeTestCase nestedXNext]

makeTestCase :: (TestCase, Word64, SMTStatus) -> TestTree
makeTestCase tce@((_, phi), _, _) = testCase tname $ tthunk phi
  where (tname, tthunk) = makeTest tce

benchs :: TestTree
benchs = testGroup "Z3Encoding Satisfiability Tests"
  $ concatMap (map makeBench) [efTests, regressionTests]

makeBench :: (TestCase, Word64, SMTStatus) -> Benchmark
makeBench tce@((_, phi), _, _) = bench bname $ nfAppIO bthunk phi
  where (bname, bthunk) = makeTest tce

makeTest :: (TestCase, Word64, SMTStatus)
         -> (String, Formula String -> Assertion)
makeTest ((name, phi), k, expected) =
  ( name ++ " (" ++ show phi ++ ")"
  , (\f -> do
        sat <- (smtStatus . DBG.traceShowId) <$> isSatisfiable False stlV2Alphabet f k
        expected @=? sat)
  )

efTests :: [(TestCase, Word64, SMTStatus)]
efTests = zip3Expected (filter (isSupported . snd) formulas) (repeat 12) expectedRes
          -- $ zip3 (filter (isSupported . snd) formulas) (repeat 12) $ repeat Sat

isSupported :: Formula a -> Bool
isSupported f = case f of
  T               -> True
  Atomic _        -> True
  Not g           -> isSupported g
  Or g h          -> isSupported g && isSupported h
  And g h         -> isSupported g && isSupported h
  Xor g h         -> isSupported g && isSupported h
  Implies g h     -> isSupported g && isSupported h
  Iff g h         -> isSupported g && isSupported h
  PNext _ g       -> isSupported g
  PBack _ _       -> False
  WPNext _ g      -> isSupported g
  XNext _ g       -> isSupported g
  XBack _ _       -> False
  WXNext _ g      -> isSupported g
  HNext _ g       -> isSupported g
  HBack _ _       -> False
  Until _ g h     -> isSupported g && isSupported h
  Release _ g h   -> isSupported g && isSupported h
  Since _ _ _     -> False
  HUntil _ g h    -> isSupported g && isSupported h
  HSince _ _ _    -> False
  Next g          -> isSupported g
  WNext g         -> isSupported g
  Back g          -> isSupported g
  WBack g         -> isSupported g
  Eventually g    -> isSupported g
  Always g        -> isSupported g
  Once g          -> isSupported g
  Historically g  -> isSupported g
  AuxBack _ _     -> False

expectedRes :: [SMTStatus]
expectedRes =
  [ Sat, Sat, Sat, Unknown, Unknown, Sat -- 5
  , Sat, Sat, Unknown -- 8
  , Sat, Sat, Unknown, Sat -- 13
  , Sat, Unknown -- 16
  , Sat, Sat, Sat, Sat, Sat, Sat -- base_tests
  , Sat, Sat -- chain_next
  , Sat, Sat, Sat, Sat -- contains_exc
  , Sat -- data_access
  , Sat -- exception_safety
  , Sat, Sat -- hier_down
  , Sat -- hier_insp
  , Sat, Sat -- hier_up
  , Sat, Sat -- normal_ret
  , Sat -- no_throw
  , Sat -- uninstall_han
  , Sat, Sat, Sat -- until_exc
  , Sat, Sat -- until_misc
  ]

regressionTests :: [(TestCase, Word64, SMTStatus)]
regressionTests = [wpnextBug, andXNext]

wpnextBug :: (TestCase, Word64, SMTStatus)
wpnextBug =
  ( ( "WPNext bug"
    , ap "call" `And` Not (PNext Down (ap "exc")) `And` PNext Up (Not (ap "ret") `And` PNext Up T))
  , 10, Sat
  )

andXNext :: (TestCase, Word64, SMTStatus)
andXNext =
  ( ("Conjoined XNexts"
    , XNext Down (ap "call") `And` XNext Up (ap "exc") `And` XNext Down (ap "p") `And` XNext Down (ap "q") `And` XNext Down (ap "w") `And` XNext Down (ap "r"))
  , 10, Sat
  )

nestedXNext :: (TestCase, Word64, SMTStatus)
nestedXNext =
  ( ("Nested XNexts"
    , XNext Down $ XNext Down $ XNext Down $ XNext Down $ ap "call")
  , 40, Sat
  )

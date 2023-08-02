{- |
   Module      : Pomc.Test.TestZ3Sat
   Copyright   : 2021-23 Michele Chiari
   License     : MIT
   Maintainer  : Michele Chiari
-}

module Pomc.Test.TestZ3Sat ( tests, isSupported ) where

import Pomc.Test.EvalFormulas (TestCase, zipExpected, formulas, ap)
import Pomc.Test.OPMs (stlV2Alphabet)
import Pomc.Z3Encoding (isSatisfiable, SMTResult(..), SMTStatus(..))
import Pomc.Potl (Formula(..), Dir(..))

import Test.Tasty
import Test.Tasty.HUnit
import Data.Word (Word64)

import qualified Debug.Trace as DBG

tests :: TestTree
tests = testGroup "Z3Encoding Satisfiability Tests" [efTests, regressionTests]

makeTestCase :: Word64
             -> (TestCase, SMTStatus)
             -> TestTree
makeTestCase k ((name, phi), expected) =
  let sat = DBG.traceShowId <$> isSatisfiable stlV2Alphabet phi k
  in testCase (name ++ " (" ++ show phi ++ ")") $ fmap smtStatus sat >>= (expected @=?)

efTests :: TestTree
efTests = testGroup "EvalFormulas"
  $ map (makeTestCase 12) --11
  $ zipExpected (filter (isSupported . snd) formulas) expectedRes
  -- $ zip (filter (isSupported . snd) formulas) $ repeat Sat

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

regressionTests :: TestTree
regressionTests = testGroup "Other Tests" [wpnextBug, nestedXNext, andXNext]

wpnextBug :: TestTree
wpnextBug = makeTestCase 10 (("WPNext bug", ap "call" `And` Not (PNext Down (ap "exc")) `And` PNext Up (Not (ap "ret") `And` PNext Up T)), Sat)

nestedXNext :: TestTree
nestedXNext = makeTestCase 40 (
  ("Nested XNexts"
  , XNext Down $ XNext Down $ XNext Down $ XNext Down $ ap "call")
  , Sat
  )

andXNext :: TestTree
andXNext = makeTestCase 10 (
  ("Conjoined XNexts"
  , XNext Down (ap "call") `And` XNext Up (ap "exc") `And` XNext Down (ap "p") `And` XNext Down (ap "q") `And` XNext Down (ap "w") `And` XNext Down (ap "r"))
  , Sat
  )

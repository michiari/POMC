{-# LANGUAGE QuasiQuotes #-}
{- |
   Module      : TestZ3MC
   Copyright   : 2021-23 Michele Chiari
   License     : MIT
   Maintainer  : Michele Chiari
-}

module TestZ3MC ( tests ) where

import TestZ3Sat (isSupported)
import TestMP hiding (tests)
import EvalFormulas (TestCase, zipExpected, formulas)
import Pomc.Potl
import Pomc.Z3Encoding (modelCheckProgram, SMTResult(..), SMTStatus(..))
import Pomc.MiniProcParse (programP)

import Test.Tasty
import Test.Tasty.HUnit
import Text.RawString.QQ
import Text.Megaparsec
import qualified Data.Text as T
import Data.Maybe (fromJust)

import qualified Debug.Trace as DBG

tests :: TestTree
tests = testGroup "Z3Encoding Model Checking Tests"
  [ sasEvalTests, nondetTrue ]

makeTestCase :: T.Text
             -> (TestCase, SMTStatus)
             -> TestTree
makeTestCase filecont ((name, phi), expected) =
  testCase (name ++ " (" ++ show phi ++ ")") assertion where
  assertion = do
    prog <- case parse (programP <* eof) name filecont of
              Left  errBundle -> assertFailure (errorBundlePretty errBundle)
              Right fsks      -> return fsks
    smtres <- modelCheckProgram phi prog 18
    DBG.traceShowM smtres
    let debugMsg | smtStatus smtres == Unsat =
                   "Expected " ++ show expected ++ ", got Unsat. Trace:\n"
                   ++ show (fromJust $ smtTableau smtres)
                 | otherwise =
                   "Expected " ++ show expected ++ ", got " ++ show (smtStatus smtres) ++ "."
    assertBool debugMsg (smtStatus smtres == expected)


sasEvalTests :: TestTree
sasEvalTests = testGroup "SAS MiniProc MC Eval Tests" $
  map (makeTestCase sasMPSource)
  $ zipExpected (filter (isSupported . snd) EvalFormulas.formulas) expectedSasEval

expectedSasEval :: [SMTStatus]
expectedSasEval =
  [ Unknown, Unsat, Unknown, Unsat, Unsat, Unsat
  , Unsat, Unsat, Unsat, Unsat, Unknown   -- base_tests
  , Unknown, Unsat, Unsat, Unknown -- contains_exc
  , Unsat                          -- normal_ret
  , Unsat, Unknown, Unknown        -- until_exc
  , Unknown, Unknown               -- until_misc
  ]

-- noHanEvalTests :: TestTree
-- noHanEvalTests = testGroup "NoHan MiniProc MC Eval Tests" $
--   map (makeTestCase noHanSource) (zipExpected EvalFormulas.formulas expectedNoHanEval)

-- simpleThenEvalTests :: TestTree
-- simpleThenEvalTests = testGroup "SimpleThen MiniProc MC Eval Tests" $
--   map (makeTestCase simpleThenSource) (zipExpected EvalFormulas.formulas expectedSimpleThenEval)

-- simpleElseEvalTests :: TestTree
-- simpleElseEvalTests = testGroup "SimpleElse MiniProc MC Eval Tests" $
--   map (makeTestCase simpleElseSource) (zipExpected EvalFormulas.formulas expectedSimpleElseEval)


nondetTrue :: TestTree
nondetTrue = testGroup "Nondeterministic Int"
  [ makeTestCase nondetSrc (("True", Not T), Unsat)
  , makeTestCase nondetSrcLong (("True", Not T), Unsat)
  , makeTestCase veryNondetSrc (("Very Nondet", Not T), Unsat)
  ]

nondetSrcLong :: T.Text
nondetSrcLong = T.pack [r|
u32 a, b, x, y;
bool assert, cover0, cover1, cover2;

main() {
  x = *;
  y = 10u32;
  a = 4u32;
  b = 2u32;
  if (x > 0u32) {
    b = a + 2u32;
    if (x < y) {
      a = (x * 2u32) + y;
      cover0 = true;
    } else {
      cover1 = true;
    }
  } else {
    cover2 = true;
  }
  assert = a != b;
}
|]

veryNondetSrc :: T.Text
veryNondetSrc = T.pack [r|
main() {
  u32 x;
  x = *;
  if (x < 4294967295u32) {
    main();
  } else {}
}
|]

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
import EvalFormulas (TestCase, zipExpected, formulas, ap)
import Pomc.Potl
import Pomc.Z3Encoding (modelCheckProgram, SMTResult(..), SMTStatus(..))
import Pomc.MiniProc (ExprProp(..))
import Pomc.Parse.Parser (CheckRequest(..), checkRequestP)
import Pomc.Parse.MiniProc (programP)

import Test.Tasty
import Test.Tasty.HUnit
import Text.RawString.QQ
import Text.Megaparsec
import qualified Data.Text as T
import Data.Maybe (fromJust)

import qualified Debug.Trace as DBG

tests :: TestTree
tests = testGroup "Z3Encoding Model Checking Tests"
  [ sasEvalTests, nondetTrue, nondetExprProp ]

makeTestCase :: T.Text
             -> (TestCase, SMTStatus)
             -> TestTree
makeTestCase filecont ((name, phi), expected) =
  testCase (name ++ " (" ++ show phi ++ ")") assertion where
  assertion = do
    prog <- case parse (programP <* eof) name filecont of
              Left  errBundle -> assertFailure (errorBundlePretty errBundle)
              Right fsks      -> return fsks
    smtres <- modelCheckProgram (fmap (TextProp . T.pack) phi) prog 18
    DBG.traceShowM smtres
    let debugMsg | smtStatus smtres == Unsat =
                   "Expected " ++ show expected ++ ", got Unsat. Trace:\n"
                   ++ show (fromJust $ smtTableau smtres)
                 | otherwise =
                   "Expected " ++ show expected ++ ", got " ++ show (smtStatus smtres) ++ "."
    assertBool debugMsg (smtStatus smtres == expected)

makeParseTestCase :: T.Text -> String -> String -> SMTStatus -> TestTree
makeParseTestCase progSource name phi expected =
  testCase (name ++ " (" ++ show phi ++ ")") assertion
  where
    filecont = T.concat [ T.pack "formulas = "
                        , T.pack phi
                        , T.pack ";\nprogram:\n"
                        , progSource
                        ]
    assertion = do
      pcreq <- case parse (checkRequestP <* eof) name filecont of
                 Left  errBundle -> assertFailure (errorBundlePretty errBundle)
                 Right pcreq      -> return pcreq
      smtres <- modelCheckProgram (head . pcreqFormulas $ pcreq) (pcreqMiniProc pcreq) 18
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
  -- $ zip (filter (isSupported . snd) EvalFormulas.formulas) $ repeat Sat

expectedSasEval :: [SMTStatus]
expectedSasEval =
  [ Unknown, Unsat, Unknown, Unsat, Unsat, Unsat -- 5
  , Unsat, Unsat, Unsat -- 8
  , Unknown, Unknown, Unsat, Unknown -- 13
  , Unknown, Unsat                 -- base_tests
  , Unknown, Unknown               -- chain_next
  , Unknown, Unsat, Unsat, Unknown -- contains_exc
  , Unknown                        -- data_access
  , Unknown                        -- exception_safety
  , Unsat, Unsat                   -- normal_ret
  , Unknown                        -- no_throw
  , Unsat                          -- ininstall_han
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
nondetTrue = testGroup "Nondeterministic Int Reachability"
  [ makeTestCase nondetSrc (("True", Not T), Unsat)
  , makeTestCase nondetSrcLong (("True", Not T), Unsat)
  , makeTestCase veryNondetSrc (("Very Nondet", Not T), Unsat)
  , makeTestCase nondetSrcLong (("Sbobinz", Not (PNext Down $ ap "stm")), Unsat)
  ]

nondetExprProp :: TestTree
nondetExprProp = testGroup "Nondeterministic Int Expressions"
  [ makeParseTestCase nondetSrcLong "a != b" "~ (PNd (PNu (PNu (PNu [main| a != b ]))))" Unsat ]

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

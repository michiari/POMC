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
import Data.Word (Word64)

import qualified Debug.Trace as DBG

tests :: TestTree
tests = testGroup "Z3Encoding Model Checking Tests"
  [ sasEvalTests, noHanEvalTests, simpleThenEvalTests, simpleElseEvalTests
  , nondetTrue, nondetExprProp, testHierD, testHierU
  ]

makeTestCase :: T.Text
             -> Word64
             -> (TestCase, SMTStatus)
             -> TestTree
makeTestCase filecont k ((name, phi), expected) =
  testCase (name ++ " (" ++ show phi ++ ")") assertion where
  assertion = do
    prog <- case parse (programP <* eof) name filecont of
              Left  errBundle -> assertFailure (errorBundlePretty errBundle)
              Right fsks      -> return fsks
    smtres <- modelCheckProgram (fmap (TextProp . T.pack) phi) prog k
    DBG.traceShowM smtres
    let debugMsg | smtStatus smtres == Unsat =
                   "Expected " ++ show expected ++ ", got Unsat. Trace:\n"
                   ++ show (fromJust $ smtTableau smtres)
                 | otherwise =
                   "Expected " ++ show expected ++ ", got " ++ show (smtStatus smtres) ++ "."
    assertBool debugMsg (smtStatus smtres == expected)

makeParseTestCase :: T.Text -> Word64 -> String -> String -> SMTStatus -> TestTree
makeParseTestCase progSource k name phi expected =
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
      smtres <- modelCheckProgram (head . pcreqFormulas $ pcreq) (pcreqMiniProc pcreq) k
      DBG.traceShowM smtres
      let debugMsg | smtStatus smtres == Unsat =
                   "Expected " ++ show expected ++ ", got Unsat. Trace:\n"
                   ++ show (fromJust $ smtTableau smtres)
                 | otherwise =
                   "Expected " ++ show expected ++ ", got " ++ show (smtStatus smtres) ++ "."
      assertBool debugMsg (smtStatus smtres == expected)


sasEvalTests :: TestTree
sasEvalTests = testGroup "SAS MiniProc MC Eval Tests" $
  map (makeTestCase sasMPSource 17)
  $ zipExpected (filter (isSupported . snd) EvalFormulas.formulas) expectedSasEval
  -- $ zip (filter (isSupported . snd) EvalFormulas.formulas) $ repeat Sat

expectedSasEval :: [SMTStatus]
expectedSasEval =
  [ Unknown, Unsat, Unknown, Unsat, Unsat, Unsat -- 5
  , Unsat, Unsat, Unsat -- 8
  , Unknown, Unknown, Unsat, Unknown -- 13
  , Unknown, Unsat -- 16
  , Unsat, Unsat, Unsat, Unsat, Unsat, Unknown -- base_tests
  , Unknown, Unknown               -- chain_next
  , Unknown, Unsat, Unsat, Unknown -- contains_exc
  , Unknown                        -- data_access
  , Unknown                        -- exception_safety
  , Unsat, Unsat                   -- hier_down
  , Unsat                          -- hier_insp
  , Unknown, Unsat                 -- hier_up
  , Unsat, Unsat                   -- normal_ret
  , Unknown                        -- no_throw
  , Unsat                          -- uninstall_han
  , Unsat, Unknown, Unknown        -- until_exc
  , Unknown, Unknown               -- until_misc
  ]

noHanEvalTests :: TestTree
noHanEvalTests = testGroup "NoHan MiniProc MC Eval Tests" $
  map (makeTestCase noHanSource 10)
  $ zipExpected (filter (isSupported . snd) EvalFormulas.formulas) expectedNoHanEval

expectedNoHanEval :: [SMTStatus]
expectedNoHanEval =
  [ Unknown, Unsat, Unknown, Unsat, Unsat, Unsat -- 5
  , Unsat, Unknown, Unsat                        -- 8
  , Unsat, Unsat, Unsat, Unsat                   -- 13
  , Unsat, Unsat                                 -- 16
  , Unknown, Unsat, Unsat, Unsat, Unsat, Unsat   -- base_tests
  , Unsat, Unsat                                 -- chain_next
  , Unsat, Unsat, Unknown, Unsat                 -- contains_exc
  , Unknown                                      -- data_access
  , Unsat                                        -- exception_safety
  , Unknown, Unsat                               -- hier_down
  , Unsat                                        -- hier_insp
  , Unsat, Unsat                                 -- hier_up
  , Unsat, Unsat                                 -- normal_ret
  , Unsat                                        -- no_throw
  , Unknown                                      -- uninstall_han
  , Unknown, Unknown, Unknown                    -- until_exc
  , Unsat, Unsat                                 -- until_misc
  ]

simpleThenEvalTests :: TestTree
simpleThenEvalTests = testGroup "SimpleThen MiniProc MC Eval Tests" $
  map (makeTestCase simpleThenSource 14)
  $ zipExpected (filter (isSupported . snd) EvalFormulas.formulas) expectedSimpleThenEval

expectedSimpleThenEval :: [SMTStatus]
expectedSimpleThenEval =
  [ Unknown, Unsat, Unknown, Unsat, Unsat, Unsat -- 5
  , Unsat, Unsat, Unsat                          -- 8
  , Unknown, Unknown, Unsat, Unknown             -- 13
  , Unknown, Unsat                               -- 16
  , Unsat, Unsat, Unsat, Unsat, Unsat, Unsat     -- base_tests
  , Unsat, Unsat                                 -- chain_next
  , Unknown, Unsat, Unsat, Unknown               -- contains_exc
  , Unknown                                      -- data_access
  , Unknown                                      -- exception_safety
  , Unsat, Unsat                                 -- hier_down
  , Unsat                                        -- hier_insp
  , Unsat, Unsat                                 -- hier_up
  , Unsat, Unsat                                 -- normal_ret
  , Unknown                                      -- no_throw
  , Unsat                                        -- uninstall_han
  , Unsat, Unsat, Unsat                          -- until_exc
  , Unsat, Unsat                                 -- until_misc
  ]

simpleElseEvalTests :: TestTree
simpleElseEvalTests = testGroup "SimpleElse MiniProc MC Eval Tests" $
  map (makeTestCase simpleElseSource 12)
  $ zipExpected (filter (isSupported . snd) EvalFormulas.formulas) expectedSimpleElseEval

expectedSimpleElseEval :: [SMTStatus]
expectedSimpleElseEval =
  [ Unknown, Unsat, Unknown, Unsat, Unsat, Unsat -- 5
  , Unsat, Unsat, Unsat                          -- 8
  , Unknown, Unknown, Unsat, Unsat               -- 13
  , Unknown, Unsat                               -- 16
  , Unsat, Unsat, Unsat, Unsat, Unsat, Unsat     -- base_tests
  , Unsat, Unsat                                 -- chain_next
  , Unknown, Unsat, Unsat, Unknown               -- contains_exc
  , Unknown                                      -- data_access
  , Unknown                                      -- exception_safety
  , Unsat, Unsat                                 -- hier_down
  , Unsat                                        -- hier_insp
  , Unsat, Unsat                                 -- hier_up
  , Unsat, Unknown                               -- normal_ret
  , Unknown                                      -- no_throw
  , Unsat                                        -- uninstall_han
  , Unsat, Unsat, Unsat                          -- until_exc
  , Unsat, Unsat                                 -- until_misc
  ]

nondetTrue :: TestTree
nondetTrue = testGroup "Nondeterministic Int Reachability"
  [ makeTestCase nondetSrc 20 (("True", Not T), Unsat)
  , makeTestCase nondetSrcLong 20 (("True", Not T), Unsat)
  , makeTestCase veryNondetSrc 20 (("Very Nondet", Not T), Unsat)
  , makeTestCase nondetSrcLong 20 (("Sbobinz", Not (PNext Down $ ap "stm")), Unsat)
  ]

nondetExprProp :: TestTree
nondetExprProp = testGroup "Nondeterministic Int Expressions"
  [ makeParseTestCase nondetSrcLong 20 "a != b" "~ (PNd (PNu (PNu (PNu [main| a != b ]))))" Unsat ]

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


testHierD :: TestTree
testHierD = testGroup "Tests for Hierarchical Down Operators"
  $ map (makeTestCase testHierDSrc 20)
  [ (("Equal, strong", HNext Down $ ap "han"), Unsat)
  , (("Equal, weak", WHNext Down $ ap "han"), Unknown)
  , (("Single next sat, strong", Next $ Next $ HNext Down $ ap "pb"), Unknown)
  , (("Single next sat, weak", Next $ Next $ WHNext Down $ ap "pb"), Unknown)
  , (("Single next unsat, strong", Next $ Next $ HNext Down $ ap "pc"), Unsat)
  , (("Single next unsat, weak", Next $ Next $ WHNext Down $ ap "pc"), Unsat)
  , (("Two nexts sat, strong", Next $ Next $ HNext Down $ HNext Down $ ap "pc"), Unknown)
  , (("Two nexts sat, weak", Next $ Next $ WHNext Down $ WHNext Down $ ap "pc"), Unknown)
  , (("Two nexts sat, mixed", Next $ Next $ HNext Down $ WHNext Down $ ap "pc"), Unknown)
  , (("Two nexts unsat, strong", Next $ Next $ HNext Down $ HNext Down $ ap "pb"), Unsat)
  , (("Two nexts unsat, weak", Next $ Next $ WHNext Down $ WHNext Down $ ap "pb"), Unsat)
  , (("Two nexts unsat, mixed", Next $ Next $ HNext Down $ WHNext Down $ ap "pb"), Unsat)
  , (("Many nexts unsat, strong", Next $ Next $ HNext Down $ HNext Down $ HNext Down $ HNext Down $ ap "pd"), Unsat)
  , (("Many nexts sat, weak", Next $ Next $ WHNext Down $ WHNext Down $ WHNext Down $ WHNext Down $ ap "pd"), Unknown)
  , (("HUntil equal", HUntil Down T $ ap "call"), Unsat)
  , (("HRelease equal", HRelease Down T $ ap "call"), Unknown)
  , (("HUntil sat, trivial", Next $ Next $ HUntil Down T $ ap "pa"), Unknown)
  , (("HRelease sat, trivial", Next $ Next $ HRelease Down T $ ap "pa"), Unknown)
  , (("HUntil sat", Next $ Next $ HUntil Down T $ ap "pc"), Unknown)
  , (("HRelease sat", Next $ Next $ HRelease Down (ap "pd") T), Unknown)
  , (("HUntil unsat", Next $ Next $ HUntil Down (Not $ ap "pa") $ ap "pd"), Unsat)
  , (("HRelease unsat", Next $ Next $ HRelease Down (Not $ ap "pa") $ ap "pd"), Unsat)
  , (("HUntil HNext rhs sat", Next $ Next $ HUntil Down T $ HNext Down $ ap "pc"), Unknown)
  , (("HRelease WHNext lhs sat", Next $ Next $ HRelease Down (WHNext Down $ ap "pd") T), Unknown)
  , (("HUntil HNext lhs sat", Next $ Next $ HUntil Down (HNext Down $ Not $ ap "pa") $ ap "pc"), Unknown)
  , (("Nested HUntil sat", Next $ Next $ HUntil Down T $ HUntil Down (Not $ ap "pa") $ ap "pc"), Unknown)
  , (("Nested HRelease sat", Next $ Next $ HRelease Down (HRelease Down (ap "pd") (Not $ ap "pa")) T), Unknown)
  ]

testHierU :: TestTree
testHierU = testGroup "Tests for Hierarchical Up Operators"
  $ map (makeTestCase testHierUSrc 22)
  [ (("Equal, strong", HNext Up $ ap "call"), Unsat)
  , (("Equal, weak", WHNext Up $ ap "call"), Unknown)
  , (("Single next sat, strong", Next $ Next $ Next $ HNext Up $ ap "pc"), Unknown)
  , (("Single next sat, weak", Next $ Next $ Next $ WHNext Up $ ap "pc"), Unknown)
  , (("Single next unsat, strong", Next $ Next $ Next $ HNext Up $ ap "pa"), Unsat)
  , (("Single next unsat, weak", Next $ Next $ Next $ WHNext Up $ ap "pa"), Unsat)
  , (("Two nexts sat, strong", Next $ Next $ Next $ HNext Up $ HNext Up $ ap "pd"), Unknown)
  , (("Two nexts sat, weak", Next $ Next $ Next $ WHNext Up $ WHNext Up $ ap "pd"), Unknown)
  , (("Two nexts sat, mixed", Next $ Next $ Next $ HNext Up $ WHNext Up $ ap "pd"), Unknown)
  , (("Two nexts unsat, strong", Next $ Next $ Next $ HNext Up $ HNext Up $ ap "pa"), Unsat)
  , (("Two nexts unsat, weak", Next $ Next $ Next $ WHNext Up $ WHNext Up $ ap "pa"), Unsat)
  , (("Two nexts unsat, mixed", Next $ Next $ Next $ HNext Up $ WHNext Up $ ap "pa"), Unsat)
  , (("Many nexts unsat, strong", Next $ Next $ Next $ HNext Up $ HNext Up $ HNext Up $ HNext Up $ ap "pe"), Unsat)
  , (("Many nexts sat, weak", Next $ Next $ Next $ WHNext Up $ WHNext Up $ WHNext Up $ WHNext Up $ ap "pe"), Unknown)
  , (("HUntil equal", HUntil Up T $ ap "call"), Unsat)
  , (("HRelease equal", HRelease Up T $ ap "call"), Unknown)
  , (("HUntil sat, trivial", Next $ Next $ Next $ HUntil Up T $ ap "pb"), Unknown)
  , (("HRelease sat, trivial", Next $ Next $ Next $ HRelease Up T $ ap "pb"), Unknown)
  , (("HUntil sat", Next $ Next $ Next $ HUntil Up T $ ap "pe"), Unknown)
  , (("HRelease sat", Next $ Next $ Next $ HRelease Up (ap "pe") T), Unknown)
  , (("HUntil unsat", Next $ Next $ Next $ HUntil Up (Not $ ap "pc") $ ap "pe"), Unsat)
  , (("HRelease unsat", Next $ Next $ Next $ HRelease Up (Not $ ap "pc") $ ap "pe"), Unsat)
  , (("HUntil HNext rhs sat", Next $ Next $ Next $ HUntil Up T $ HNext Up $ ap "pe"), Unknown)
  , (("HRelease WHNext lhs sat", Next $ Next $ Next $ HRelease Up (WHNext Up $ ap "pe") T), Unknown)
  , (("HUntil HNext lhs sat", Next $ Next $ Next $ HUntil Up (HNext Up $ Not $ ap "pb") $ ap "pe"), Unknown)
  , (("Nested HUntil sat", Next $ Next $ Next $ HUntil Up T $ HUntil Up (Not $ ap "pc") $ ap "pe"), Unknown)
  , (("Nested HRelease sat", Next $ Next $ Next $ HRelease Up (HRelease Up (ap "pe") (Not $ ap "pc")) T), Unknown)
  ]

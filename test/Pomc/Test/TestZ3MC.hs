{-# LANGUAGE QuasiQuotes #-}
{- |
   Module      : Pomc.Test.TestZ3MC
   Copyright   : 2021-23 Michele Chiari
   License     : MIT
   Maintainer  : Michele Chiari
-}

module Pomc.Test.TestZ3MC ( tests ) where

import Pomc.Test.TestZ3Sat (isSupported)
import Pomc.Test.TestMP hiding (tests)
import Pomc.Test.EvalFormulas as EvalFormulas (TestCase, zipExpected, formulas, ap)
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
  , singleWhile, exprsTests, intTests, exprPropTests
  , testHierD, testHierU
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

singleWhile :: TestTree
singleWhile = makeTestCase simpleWhileSource 12
  (("Single-Iteration While Loop"
   , Not $ Until Down T (ap "call"
                         `And` ap "pb"
                         `And` (HNext Up $ HUntil Up T (ap "call" `And` ap "pb"))))
  , Unknown)

exprsTests :: TestTree
exprsTests = testGroup "BoolExpr Tests"
  [ makeTestCase exprsSource 20 (("Check Or BoolExpr", Until Down T (ap "call" `And` ap "pb")), Unknown)
  , makeTestCase exprsSource 20 (("Check Or Not BoolExpr", Until Down T (ap "call" `And` ap "pc")), Unknown)
  , makeTestCase exprsSource 20 (("Check And Not BoolExpr", Until Down T (ap "call" `And` ap "pd")), Unsat)
  ]

intTests :: TestTree
intTests = testGroup "Int Variables Tests" [ u8Arith1Tests
                                           , u8Arith2Tests
                                           , arithCastsTests
                                           , nondetTests
                                           , nondetTrue
                                           , nondetExprProp
                                           , arrayTests
                                           , arrayLoopTests
                                           , localTests
                                           , argTests
                                           ]

u8Arith1Tests :: TestTree
u8Arith1Tests = testGroup "u8Arith1"
  [ makeTestCase u8Arith1Src 12 (("Throws.", Until Up T (ap "exc")), Unknown)
  , makeTestCase u8Arith1Src 12 (("Terminates normally.", Until Up T (ap "ret")), Unsat)
  , makeParseTestCase u8Arith1Src 12 "Variable a is non-zero at the end." "XNu [|a]" Unknown
  ]

u8Arith2Tests :: TestTree
u8Arith2Tests = testGroup "u8Arith2"
  [ makeTestCase u8Arith2Src 18 (("Terminates normally.", Until Up T (ap "ret")), Unknown)
  , makeParseTestCase u8Arith2Src 18 "Assert true." "T Uu (ret && [|assert])" Unknown
  , makeParseTestCase u8Arith2Src 18 "Assert false." "T Uu (ret && ~[|assert])" Unsat
  ]

arithCastsTests :: TestTree
arithCastsTests = testGroup "ArithCasts"
  [ makeParseTestCase arithCastsSrc 24 "a + c > 1024u16" "T Ud (ret && [|assert1])" Unknown
  , makeParseTestCase arithCastsSrc 24 "b + d < 0s8" "T Ud (ret && [|assert2])" Unknown
  , makeParseTestCase arithCastsSrc 24 "f == 25u8" "T Ud (ret && [|assert3])" Unknown
  , makeParseTestCase arithCastsSrc 24 "b * c == 10240s16" "T Ud (ret && [|assert4])" Unknown
  , makeParseTestCase arithCastsSrc 24 "d / b == -1s8" "T Ud (ret && [|assert5])" Unknown
  ]

nondetTests :: TestTree
nondetTests = testGroup "Nondeterministic Int"
  [ makeParseTestCase nondetSrc 18 "Coverage 0" "XNd (ret && [|cover0])" Unsat
  , makeParseTestCase nondetSrc 18 "Coverage 1" "XNd (ret && [|cover1])" Unsat
  , makeParseTestCase nondetSrc 18 "Coverage 2" "XNd (ret && [|cover2])" Unsat
  , makeParseTestCase nondetSrc 18 "Assert true." "T Uu (ret && [|assert])" Unknown
  ]

nondetTrue :: TestTree
nondetTrue = testGroup "Nondeterministic Int Reachability"
  [ makeTestCase nondetSrc 20 (("True", Not T), Unsat)
  , makeTestCase nondetSrcLong 20 (("True", Not T), Unsat)
  , makeTestCase veryNondetSrc 20 (("Very Nondet", Not T), Unsat)
  , makeTestCase nondetSrcLong 20 (("Not stm", Not (PNext Down $ ap "stm")), Unsat)
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

arrayTests :: TestTree
arrayTests = testGroup "Int Array Tests"
  [ makeParseTestCase arraySrc 18 "Coverage 0" "XNd (ret && ~[|cover0])" Unsat
  , makeParseTestCase arraySrc 18 "Coverage 1" "XNd (ret && ~[|cover1])" Unsat
  , makeParseTestCase arraySrc 18 "Assert 0" "XNd (ret && [|assert0])" Unknown
  ]

arrayLoopTests :: TestTree
arrayLoopTests = testGroup "Int Array Loop Tests"
  [ makeParseTestCase arrayLoopSrc 100 "Assert 0" "XNd (ret && [|assert0])" Unknown ]

localTests :: TestTree
localTests = testGroup "Local Variables Tests"
  [ makeParseTestCase localTestsSrc 40 "Assert A" "T Ud (ret && [pA|assertA])" Unknown
  , makeParseTestCase localTestsSrc 40 "Assert B" "T Ud (ret && [pB|assertB])" Unknown
  , makeParseTestCase localTestsSrc 40 "Assert C" "T Ud (ret && [pC|assertC])" Unsat
  ]

argTests :: TestTree
argTests = testGroup "Function Arguments Tests"
  [ makeParseTestCase argTestsSrc 55 "Assert Main 0" "T Ud (ret && [main|assertMain0])" Unknown
  , makeParseTestCase argTestsSrc 55 "Assert Main 1" "T Ud (ret && [main|assertMain1])" Unknown
  , makeParseTestCase argTestsSrc 55 "Assert A 0" "T Ud (ret && [pA|assertA0])" Unknown
  , makeParseTestCase argTestsSrc 55 "Assert A 1" "T Ud (ret && [pA|assertA1])" Unknown
  , makeParseTestCase argTestsSrc 55 "Assert B 0" "T Ud (ret && [pB|assertB0])" Unknown
  , makeParseTestCase argTestsSrc 55 "Assert B 1" "T Ud (ret && [pB|assertB1])" Unknown
  ]

exprPropTests :: TestTree
exprPropTests = testGroup "Expression Propositions Tests"
  [ makeParseTestCase exprPropTestsSrc 45 "Assert Main 0" "T Ud (stm && [main| a + b + c[0u8] + c[1u8] == 28u8 ])" Unknown
  , makeParseTestCase exprPropTestsSrc 45 "Assert Main 1" "T Ud (ret && [main|a + b + c[0u8] + c[1u8] + w == 84u8])" Unknown
  , makeParseTestCase exprPropTestsSrc 45 "Assert A 0" "T Ud (stm && [pA| u == 70u8 ])" Unknown
  , makeParseTestCase exprPropTestsSrc 45 "Assert A 1" "T Ud (ret && [pA| u == 13u8])" Unknown
  , makeParseTestCase exprPropTestsSrc 45 "Assert B 0" "T Ud (stm && [pB| w + r + s + t[0u8] + t[1u8] + x == 29u8 ])" Unknown
  , makeParseTestCase exprPropTestsSrc 45 "Assert B 1" "T Ud (ret && [pB| w + r + s + t[0u8] + t[1u8] + x == 90u8 ])" Unknown
  ]

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

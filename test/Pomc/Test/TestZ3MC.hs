{-# LANGUAGE QuasiQuotes #-}
{- |
   Module      : Pomc.Test.TestZ3MC
   Copyright   : 2021-23 Michele Chiari
   License     : MIT
   Maintainer  : Michele Chiari
-}

module Pomc.Test.TestZ3MC ( tests, slowTests, benchs ) where

import Pomc.Test.TestZ3Sat (isSupported)
import Pomc.Test.TestMP hiding (tests, benchs)
import Pomc.Test.EvalFormulas as EvalFormulas (TestCase, zip3Expected, excludeIndices, formulas, ap)
import Pomc.Potl
import Pomc.Z3Encoding (SMTOpts(..), defaultSmtOpts, modelCheckProgram, SMTResult(..), SMTStatus(..))
import Pomc.MiniProc (ExprProp(..))
import Pomc.Parse.Parser (CheckRequest(..), checkRequestP)
import Pomc.Parse.MiniProc (programP)

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.Bench
import Text.RawString.QQ
import Text.Megaparsec
import qualified Data.Text as T
import Data.Maybe (fromJust)
import Data.Word (Word64)

-- import qualified Debug.Trace as DBG

tests :: TestTree
tests = testGroup "Z3Encoding Model Checking Tests"
  [ sasEvalTests, noHanEvalTests, simpleThenEvalTests, simpleElseEvalTests
  , singleWhileTest, exprsTests, intTests, exprPropTests
  , testHierDTests, testHierUTests
  ]

slowTests :: TestTree
slowTests = testGroup "Z3Encoding Model Checking Tests"
  [ sasEvalSlowTests, testHierDTestsSlow, noHanEvalSlowTests ]

makeTestCase :: T.Text -> (TestCase, Word64, SMTStatus) -> TestTree
makeTestCase filecont tce@((_, phi), _, _) = testCase tname $ tthunk phi
  where (tname, tthunk) = makeTest filecont tce

benchs :: TestTree
benchs = testGroup "Z3Encoding Model Checking Tests"
  [ sasEvalBenchs, noHanEvalBenchs, simpleThenEvalBenchs, simpleElseEvalBenchs
  , singleWhileBench, exprsBenchs, intBenchs, exprPropBenchs
  , testHierDBenchs, testHierUBenchs
  ]

makeBench :: T.Text -> (TestCase, Word64, SMTStatus) -> TestTree
makeBench filecont tce@((_, phi), _, _) = bench bname $ nfAppIO bthunk phi
  where (bname, bthunk) = makeTest filecont tce

makeTest :: T.Text -> (TestCase, Word64, SMTStatus) -> (String, Formula String -> Assertion)
makeTest filecont ((name, phi), k, expected) =
  (name ++ " (" ++ show phi ++ ")", assertion)
  where assertion f = do
          prog <- case parse (programP <* eof) name filecont of
                    Left  errBundle -> assertFailure (errorBundlePretty errBundle)
                    Right fsks      -> return fsks
          smtres <- modelCheckProgram ((defaultSmtOpts k) {-smtVerbose = True-}) (fmap (TextProp . T.pack) f) prog
          -- DBG.traceShowM smtres
          let debugMsg | smtStatus smtres == Unsat =
                         "Expected " ++ show expected ++ ", got Unsat. Trace:\n"
                         ++ show (fromJust $ smtTableau smtres)
                       | otherwise =
                         "Expected " ++ show expected ++ ", got " ++ show (smtStatus smtres) ++ "."
          assertBool debugMsg (smtStatus smtres == expected)

makeParseTestCase :: T.Text -> ((String, String), Word64, SMTStatus) -> TestTree
makeParseTestCase filecont tce@((_, phi), _, _) = testCase tname $ tthunk phi
  where (tname, tthunk) = makeParseTest filecont tce

makeParseBench :: T.Text -> ((String, String), Word64, SMTStatus) -> TestTree
makeParseBench filecont tce@((_, phi), _, _) = bench bname $ nfAppIO bthunk phi
  where (bname, bthunk) = makeParseTest filecont tce

makeParseTest :: T.Text -> ((String, String), Word64, SMTStatus)
              -> (String, String -> Assertion)
makeParseTest progSource ((name, phi), k, expected) =
  (name ++ " (" ++ show phi ++ ")", assertion)
  where
    filecont f = T.concat [ T.pack "formulas = "
                          , T.pack f
                          , T.pack ";\nprogram:\n"
                          , progSource
                          ]
    assertion f = do
      pcreq <- case parse (checkRequestP <* eof) name (filecont f) of
                 Left  errBundle -> assertFailure (errorBundlePretty errBundle)
                 Right pcreq      -> return pcreq
      smtres <- modelCheckProgram (defaultSmtOpts k) (head . pcreqFormulas $ pcreq) (pcreqMiniProc pcreq)
      -- DBG.traceShowM smtres
      let debugMsg | smtStatus smtres == Unsat =
                   "Expected " ++ show expected ++ ", got Unsat. Trace:\n"
                   ++ show (fromJust $ smtTableau smtres)
                 | otherwise =
                   "Expected " ++ show expected ++ ", got " ++ show (smtStatus smtres) ++ "."
      assertBool debugMsg (smtStatus smtres == expected)


sasEvalTests :: TestTree
sasEvalTests = testGroup "SAS MiniProc MC Eval Tests" -- k <= 25
  $ map (makeTestCase sasMPSource)
  $ filter (\((name, _), _, _) -> read (take 2 name) `notElem` sasSlow) sasEval

sasEvalBenchs :: TestTree
sasEvalBenchs = testGroup "SAS MiniProc MC Eval Tests"
  $ map (makeBench sasMPSource)
  $ filter (\((name, _), _, _) -> read (take 2 name) `notElem` sasSlow) sasEval

sasEvalSlowTests :: TestTree
sasEvalSlowTests = testGroup "SAS MiniProc MC Eval Tests"
  $ map (makeTestCase sasMPSource)
  $ filter (\((name, _), _, _) -> read (take 2 name) `elem` sasSlow) sasEval

sasEval :: [(TestCase, Word64, SMTStatus)]
sasEval = zip3Expected (filter (isSupported . snd) EvalFormulas.formulas) (repeat 55) expectedSasEval

sasSlow :: [Int]
sasSlow = [11, 15, 23, 25, 32, 33, 38, 51, 57, 58, 60, 62]

expectedSasEval :: [SMTStatus]
expectedSasEval =
  [ Sat, Unsat, Sat, Unsat, Unsat, Unsat                          -- 5
  , Unsat, Unsat, Unsat                                           -- 8
  , Sat, Sat, Unsat, Sat                                          -- 13
  , Sat, Unsat                                                    -- 16
  , Unsat, Unsat, Unsat, Unsat, Unsat, Sat                        -- base_tests
  , Sat, Sat                                                      -- chain_next
  , Sat, Unsat, Unsat, Sat                                        -- contains_exc
  , Unknown {-up to 175, Sat-}                                    -- data_access
  , Unknown {-up to 180, Sat-}                                    -- exception_safety
  , Unsat, Unsat                                                  -- hier_down
  , Unsat                                                         -- hier_insp
  , Sat, Unsat                                                    -- hier_up
  , Unsat, Unsat                                                  -- normal_ret
  , Unknown {-up to 84, Sat-}                                     -- no_throw
  , Unsat                                                         -- uninstall_han
  , Unsat, Unknown {-up to 219, Sat-}, Unknown {-up to 310, Sat-} -- until_exc
  , Sat, Unknown {-up to 229, Sat-}                               -- until_misc
  ]

noHanEvalTests :: TestTree
noHanEvalTests = testGroup "NoHan MiniProc MC Eval Tests"
  $ map (makeTestCase noHanSource)
  $ filter (\((name, _), _, _) -> read (take 2 name) `notElem` noHanSlow) noHanEval

noHanEvalBenchs :: TestTree
noHanEvalBenchs = testGroup "NoHan MiniProc MC Eval Tests"
  $ map (makeBench noHanSource)
  $ filter (\((name, _), _, _) -> read (take 2 name) `notElem` noHanSlow) noHanEval

noHanEvalSlowTests :: TestTree
noHanEvalSlowTests = testGroup "NoHan MiniProc MC Eval Tests"
  $ map (makeTestCase noHanSource)
  $ filter (\((name, _), _, _) -> read (take 2 name) `elem` noHanSlow) noHanEval

noHanEval :: [(TestCase, Word64, SMTStatus)]
noHanEval = zip3Expected (filter (isSupported . snd) EvalFormulas.formulas) (repeat 42) expectedNoHanEval

noHanSlow :: [Int]
noHanSlow = [31, 33, 55, 56, 57, 58]

expectedNoHanEval :: [SMTStatus]
expectedNoHanEval =
  [ Sat, Unsat, Sat, Unsat, Unsat, Unsat                                               -- 5
  , Unsat, Sat, Unsat                                                                  -- 8
  , Unsat, Unsat, Unsat, Unsat                                                         -- 13
  , Unsat, Unsat                                                                       -- 16
  , Unknown {-up to 175, Sat-}, Unsat, Unsat, Unsat, Unsat, Unsat                      -- base_tests
  , Unsat, Unsat                                                                       -- chain_next
  , Unsat, Unsat, Unknown {-up to 56, Sat-}, Unsat                                     -- contains_exc
  , Unknown {-up to 172, Sat-}                                                         -- data_access
  , Unsat                                                                              -- exception_safety
  , Sat, Unsat                                                                         -- hier_down
  , Unsat                                                                              -- hier_insp
  , Unsat, Unsat                                                                       -- hier_up
  , Unsat, Unsat                                                                       -- normal_ret
  , Unsat                                                                              -- no_throw
  , Sat                                                                                -- uninstall_han
  , Unknown {-up to 128, Sat-}, Unknown {-up to 189, Sat-}, Unknown {-up to 100, Sat-} -- until_exc
  , Unsat, Unsat                                                                       -- until_misc
  ]

simpleThenEvalTests :: TestTree
simpleThenEvalTests = testGroup "SimpleThen MiniProc MC Eval Tests" $
  map (makeTestCase simpleThenSource)
  $ zip3Expected (filter (isSupported . snd) EvalFormulas.formulas) (repeat 500) expectedSimpleThenEval

simpleThenEvalBenchs :: TestTree
simpleThenEvalBenchs = testGroup "SimpleThen MiniProc MC Eval Tests" $
  map (makeBench simpleThenSource)
  $ zip3Expected (filter (isSupported . snd) EvalFormulas.formulas) (repeat 14) expectedSimpleThenEval

expectedSimpleThenEval :: [SMTStatus]
expectedSimpleThenEval =
  [ Sat, Unsat, Sat, Unsat, Unsat, Unsat           -- 5
  , Unsat, Unsat, Unsat                            -- 8
  , Sat, Sat, Unsat, Sat                           -- 13
  , Sat, Unsat                                     -- 16
  , Unsat, Unsat, Unsat, Unsat, Unsat, Unsat       -- base_tests
  , Unsat, Unsat                                   -- chain_next
  , Sat, Unsat, Unsat, Unknown {-Sat-}             -- contains_exc
  , Unknown {-Sat-}                                -- data_access
  , Unknown {-Sat-}                                -- exception_safety
  , Unsat, Unsat                                   -- hier_down
  , Unsat                                          -- hier_insp
  , Unsat, Unsat                                   -- hier_up
  , Unsat, Unsat                                   -- normal_ret
  , Unknown {-Sat-}                                -- no_throw
  , Unsat                                          -- uninstall_han
  , Unsat, Unsat, Unsat                            -- until_exc
  , Unsat, Unsat                                   -- until_misc
  ]

simpleElseEvalTests :: TestTree
simpleElseEvalTests = testGroup "SimpleElse MiniProc MC Eval Tests" $
  map (makeTestCase simpleElseSource)
  $ zip3Expected (filter (isSupported . snd) EvalFormulas.formulas) (repeat 500) expectedSimpleElseEval

simpleElseEvalBenchs :: TestTree
simpleElseEvalBenchs = testGroup "SimpleElse MiniProc MC Eval Tests" $
  map (makeTestCase simpleElseSource)
  $ zip3Expected (filter (isSupported . snd) EvalFormulas.formulas) (repeat 12) expectedSimpleElseEval

expectedSimpleElseEval :: [SMTStatus]
expectedSimpleElseEval =
  [ Sat, Unsat, Sat, Unsat, Unsat, Unsat     -- 5
  , Unsat, Unsat, Unsat                      -- 8
  , Sat, Sat, Unsat, Unsat                   -- 13
  , Sat, Unsat                               -- 16
  , Unsat, Unsat, Unsat, Unsat, Unsat, Unsat -- base_tests
  , Unsat, Unsat                             -- chain_next
  , Sat, Unsat, Unsat, Sat                   -- contains_exc
  , Sat                                      -- data_access
  , Sat                                      -- exception_safety
  , Unsat, Unsat                             -- hier_down
  , Unsat                                    -- hier_insp
  , Unsat, Unsat                             -- hier_up
  , Unsat, Sat                               -- normal_ret
  , Sat                                      -- no_throw
  , Unsat                                    -- uninstall_han
  , Unsat, Unsat, Unsat                      -- until_exc
  , Unsat, Unsat                             -- until_misc
  ]


singleWhileTest :: TestTree
singleWhileTest = makeTestCase simpleWhileSource singleWhile

singleWhileBench :: TestTree
singleWhileBench = makeBench simpleWhileSource singleWhile

singleWhile :: (TestCase, Word64, SMTStatus)
singleWhile =
  (("Single-Iteration While Loop"
   , Not $ Until Down T (ap "call"
                         `And` ap "pb"
                         `And` (HNext Up $ HUntil Up T (ap "call" `And` ap "pb"))))
  , 12, Sat)

exprsTests :: TestTree
exprsTests = testGroup "BoolExpr Tests" $ map (makeTestCase exprsSource) exprsTestCases

exprsBenchs :: TestTree
exprsBenchs = testGroup "BoolExpr Tests" $ map (makeBench exprsSource) exprsTestCases

exprsTestCases :: [(TestCase, Word64, SMTStatus)]
exprsTestCases =
  [ (("Check Or BoolExpr", Until Down T (ap "call" `And` ap "pb")), 20, Sat)
  , (("Check Or Not BoolExpr", Until Down T (ap "call" `And` ap "pc")), 20, Sat)
  , (("Check And Not BoolExpr", Until Down T (ap "call" `And` ap "pd")), 20, Unsat)
  ]

intTests :: TestTree
intTests = testGroup "Int Variables Tests"
  [ testGroup "u8Arith1" $ map (makeParseTestCase u8Arith1Src) u8Arith1Tests
  , testGroup "u8Arith2" $ map (makeParseTestCase u8Arith2Src) u8Arith2Tests
  , testGroup "ArithCasts" $ map (makeParseTestCase arithCastsSrc) arithCastsTests
  , testGroup "Nondeterministic Int"
    $ map (makeParseTestCase nondetSrc) nondetTests
  , testGroup "Nondeterministic Int Reachability"
    $ map (uncurry makeTestCase) nondetTrue
  , testGroup "Nondeterministic Int Expressions"
    $ map (makeParseTestCase nondetSrcLong) nondetExprProp
  , testGroup "Int Array Tests" $ map (makeParseTestCase arraySrc) arrayTests
  , testGroup "Int Array Loop Tests" $ map (makeParseTestCase arrayLoopSrc) arrayLoopTests
  , testGroup "Local Variables Tests" $ map (makeParseTestCase localTestsSrc) localTests
  , testGroup "Function Arguments Tests" $ map (makeParseTestCase argTestsSrc) argTests
  ]

intBenchs :: TestTree
intBenchs = testGroup "Int Variables Tests"
  [ testGroup "u8Arith1" $ map (makeParseBench u8Arith1Src) u8Arith1Tests
  , testGroup "u8Arith2" $ map (makeParseBench u8Arith2Src) u8Arith2Tests
  , testGroup "ArithCasts" $ map (makeParseBench arithCastsSrc) arithCastsTests
  , testGroup "Nondeterministic Int"
    $ map (makeParseBench nondetSrc) nondetTests
  , testGroup "Nondeterministic Int Reachability"
    $ map (uncurry makeTestCase) nondetTrue
  , testGroup "Nondeterministic Int Expressions"
    $ map (makeParseBench nondetSrcLong) nondetExprProp
  , testGroup "Int Array Tests" $ map (makeParseBench arraySrc) arrayTests
  , testGroup "Int Array Loop Tests" $ map (makeParseBench arrayLoopSrc) arrayLoopTests
  , testGroup "Local Variables Tests" $ map (makeParseBench localTestsSrc) localTests
  , testGroup "Function Arguments Tests" $ map (makeParseBench argTestsSrc) argTests
  ]

u8Arith1Tests :: [((String, String), Word64, SMTStatus)]
u8Arith1Tests =
  [ (("Throws.", "T Uu exc"), 12, Sat)
  , (("Terminates normally.", "T Uu ret"), 12, Unsat)
  , (("Variable a is non-zero at the end.", "XNu [|a]"), 12, Sat)
  ]

u8Arith2Tests :: [((String, String), Word64, SMTStatus)]
u8Arith2Tests =
  [ (("Terminates normally.", "T Uu ret"), 18, Sat)
  , (("Assert true.", "T Uu (ret && [|assert])"), 18, Sat)
  , (("Assert false.", "T Uu (ret && ~[|assert])"), 18, Unsat)
  ]

arithCastsTests :: [((String, String), Word64, SMTStatus)]
arithCastsTests =
  [ (("a + c > 1024u16", "T Ud (ret && [|assert1])"), 24, Sat)
  , (("b + d < 0s8", "T Ud (ret && [|assert2])"), 24, Sat)
  , (("f == 25u8", "T Ud (ret && [|assert3])"), 24, Sat)
  , (("b * c == 10240s16", "T Ud (ret && [|assert4])"), 24, Sat)
  , (("d / b == -1s8", "T Ud (ret && [|assert5])"), 24, Sat)
  ]

nondetTests :: [((String, String), Word64, SMTStatus)]
nondetTests =
  [ (("Coverage 0", "XNd (ret && [|cover0])"), 18, Unsat)
  , (("Coverage 1", "XNd (ret && [|cover1])"), 18, Unsat)
  , (("Coverage 2", "XNd (ret && [|cover2])"), 18, Unsat)
  , (("Assert true.", "T Uu (ret && [|assert])"), 20, Sat)
  ]

nondetTrue :: [(T.Text, (TestCase, Word64, SMTStatus))]
nondetTrue =
  [ (nondetSrc, (("True", Not T), 20, Unsat))
  , (nondetSrcLong, (("True", Not T), 20, Unsat))
  , (veryNondetSrc, (("Very Nondet", Not T), 20, Unsat))
  , (nondetSrcLong, (("Not stm", Not (PNext Down $ ap "stm")), 20, Unsat))
  ]

nondetExprProp :: [((String, String), Word64, SMTStatus)]
nondetExprProp =
  [ (("a != b", "~ (PNd (PNu (PNu (PNu [main| a != b ]))))"), 20, Unsat) ]

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

arrayTests :: [((String, String), Word64, SMTStatus)]
arrayTests =
  [ (("Coverage 0", "XNd (ret && ~[|cover0])"), 18, Unsat)
  , (("Coverage 1", "XNd (ret && ~[|cover1])"), 18, Unsat)
  , (("Assert 0", "XNd (ret && [|assert0])"), 18, Sat)
  ]

arrayLoopTests :: [((String, String), Word64, SMTStatus)]
arrayLoopTests =
  [ (("Assert 0", "XNd (ret && [|assert0])"), 100, Sat) ]

localTests :: [((String, String), Word64, SMTStatus)]
localTests =
  [ (("Assert A", "T Ud (ret && [pA|assertA])"), 40, Sat)
  , (("Assert B", "T Ud (ret && [pB|assertB])"), 40, Sat)
  , (("Assert C", "T Ud (ret && [pC|assertC])"), 40, Unsat)
  ]

argTests :: [((String, String), Word64, SMTStatus)]
argTests =
  [ (("Assert Main 0", "T Ud (ret && [main|assertMain0])"), 55, Sat)
  , (("Assert Main 1", "T Ud (ret && [main|assertMain1])"), 55, Sat)
  , (("Assert A 0", "T Ud (ret && [pA|assertA0])"), 55, Sat)
  , (("Assert A 1", "T Ud (ret && [pA|assertA1])"), 55, Sat)
  , (("Assert B 0", "T Ud (ret && [pB|assertB0])"), 55, Sat)
  , (("Assert B 1", "T Ud (ret && [pB|assertB1])"), 55, Sat)
  ]

exprPropTests :: TestTree
exprPropTests = testGroup "Expression Propositions Tests"
  $ map (makeParseTestCase exprPropTestsSrc) exprProp

exprPropBenchs :: TestTree
exprPropBenchs = testGroup "Expression Propositions Tests"
  $ map (makeParseBench exprPropTestsSrc) exprProp

exprProp :: [((String, String), Word64, SMTStatus)]
exprProp =
  [ (("Assert Main 0", "T Ud (stm && [main| a + b + c[0u8] + c[1u8] == 28u8 ])"), 45, Sat)
  , (("Assert Main 1", "T Ud (ret && [main|a + b + c[0u8] + c[1u8] + w == 84u8])"), 45, Sat)
  , (("Assert A 0", "T Ud (stm && [pA| u == 70u8 ])"), 45, Sat)
  , (("Assert A 1", "T Ud (ret && [pA| u == 13u8])"), 45, Sat)
  , (("Assert B 0", "T Ud (stm && [pB| w + r + s + t[0u8] + t[1u8] + x == 29u8 ])"), 45, Sat)
  , (("Assert B 1", "T Ud (ret && [pB| w + r + s + t[0u8] + t[1u8] + x == 90u8 ])"), 45, Sat)
  ]

testHierDTests :: TestTree
testHierDTests = testGroup "Tests for Hierarchical Down Operators"
 $ map (makeTestCase testHierDSrc) $ excludeIndices testHierD [2, 3]

testHierDTestsSlow :: TestTree
testHierDTestsSlow = testGroup "Tests for Hierarchical Down Operators"
 $ map (makeTestCase testHierDSrc) $ fmap (testHierD !!) [2, 3]

testHierDBenchs :: TestTree
testHierDBenchs = testGroup "Tests for Hierarchical Down Operators"
 $ map (makeBench testHierDSrc) testHierD

testHierD :: [(TestCase, Word64, SMTStatus)]
testHierD =
  [ (("Equal, strong", HNext Down $ ap "han"), 20, Unsat)
  , (("Equal, weak", WHNext Down $ ap "han"), 25, Sat)
  , (("Single next sat, strong", Next $ Next $ HNext Down $ ap "pb"), 57, Sat)
  , (("Single next sat, weak", Next $ Next $ WHNext Down $ ap "pb"), 55, Sat)
  , (("Single next unsat, strong", Next $ Next $ HNext Down $ ap "pc"), 20, Unsat)
  , (("Single next unsat, weak", Next $ Next $ WHNext Down $ ap "pc"), 20, Unsat)
  , (("Two nexts sat, strong", Next $ Next $ HNext Down $ HNext Down $ ap "pc"), 500, Unknown {-Sat-})
  , (("Two nexts sat, weak", Next $ Next $ WHNext Down $ WHNext Down $ ap "pc"), 500, Unknown {-Sat-})
  , (("Two nexts sat, mixed", Next $ Next $ HNext Down $ WHNext Down $ ap "pc"), 500, Unknown {-Sat-})
  , (("Two nexts unsat, strong", Next $ Next $ HNext Down $ HNext Down $ ap "pb"), 20, Unsat)
  , (("Two nexts unsat, weak", Next $ Next $ WHNext Down $ WHNext Down $ ap "pb"), 20, Unsat)
  , (("Two nexts unsat, mixed", Next $ Next $ HNext Down $ WHNext Down $ ap "pb"), 20, Unsat)
  , (("Many nexts unsat, strong", Next $ Next $ HNext Down $ HNext Down $ HNext Down $ HNext Down $ ap "pd"), 20, Unsat)
  , (("Many nexts sat, weak", Next $ Next $ WHNext Down $ WHNext Down $ WHNext Down $ WHNext Down $ ap "pd"), 500, Unknown {-Sat-}) -- Unknown up to 200
  , (("HUntil equal", HUntil Down T $ ap "call"), 20, Unsat)
  , (("HRelease equal", HRelease Down T $ ap "call"), 20, Sat)
  , (("HUntil sat, trivial", Next $ Next $ HUntil Down T $ ap "pa"), 500, Unknown {-Sat-})
  , (("HRelease sat, trivial", Next $ Next $ HRelease Down T $ ap "pa"), 20, Sat)
  , (("HUntil sat", Next $ Next $ HUntil Down T $ ap "pc"), 500, Unknown {-Sat-})
  , (("HRelease sat", Next $ Next $ HRelease Down (ap "pd") T), 500, Unknown {-Sat-})
  , (("HUntil unsat", Next $ Next $ HUntil Down (Not $ ap "pa") $ ap "pd"), 20, Unsat)
  , (("HRelease unsat", Next $ Next $ HRelease Down (Not $ ap "pa") $ ap "pd"), 20, Unsat)
  , (("HUntil HNext rhs sat", Next $ Next $ HUntil Down T $ HNext Down $ ap "pc"), 500, Unknown {-Sat-})
  , (("HRelease WHNext lhs sat", Next $ Next $ HRelease Down (WHNext Down $ ap "pd") T), 500, Unknown {-Sat-})
  , (("HUntil HNext lhs sat", Next $ Next $ HUntil Down (HNext Down $ Not $ ap "pa") $ ap "pc"), 500, Unknown {-Sat-})
  , (("Nested HUntil sat", Next $ Next $ HUntil Down T $ HUntil Down (Not $ ap "pa") $ ap "pc"), 500, Unknown {-Sat-})
  , (("Nested HRelease sat", Next $ Next $ HRelease Down (HRelease Down (ap "pd") (Not $ ap "pa")) T), 500, Unknown {-Sat-})
  ]

testHierUTests :: TestTree
testHierUTests = testGroup "Tests for Hierarchical Up Operators"
  $ map (makeTestCase testHierUSrc) testHierU

testHierUBenchs :: TestTree
testHierUBenchs = testGroup "Tests for Hierarchical Up Operators"
  $ map (makeBench testHierUSrc) testHierU

testHierU :: [(TestCase, Word64, SMTStatus)]
testHierU =
  [ (("Equal, strong", HNext Up $ ap "call"), 22, Unsat)
  , (("Equal, weak", WHNext Up $ ap "call"), 22, Sat)
  , (("Single next sat, strong", Next $ Next $ Next $ HNext Up $ ap "pc"), 22, Sat)
  , (("Single next sat, weak", Next $ Next $ Next $ WHNext Up $ ap "pc"), 22, Sat)
  , (("Single next unsat, strong", Next $ Next $ Next $ HNext Up $ ap "pa"), 22, Unsat)
  , (("Single next unsat, weak", Next $ Next $ Next $ WHNext Up $ ap "pa"), 22, Unsat)
  , (("Two nexts sat, strong", Next $ Next $ Next $ HNext Up $ HNext Up $ ap "pd"), 22, Sat)
  , (("Two nexts sat, weak", Next $ Next $ Next $ WHNext Up $ WHNext Up $ ap "pd"), 22, Sat)
  , (("Two nexts sat, mixed", Next $ Next $ Next $ HNext Up $ WHNext Up $ ap "pd"), 22, Sat)
  , (("Two nexts unsat, strong", Next $ Next $ Next $ HNext Up $ HNext Up $ ap "pa"), 22, Unsat)
  , (("Two nexts unsat, weak", Next $ Next $ Next $ WHNext Up $ WHNext Up $ ap "pa"), 22, Unsat)
  , (("Two nexts unsat, mixed", Next $ Next $ Next $ HNext Up $ WHNext Up $ ap "pa"), 22, Unsat)
  , (("Many nexts unsat, strong", Next $ Next $ Next $ HNext Up $ HNext Up $ HNext Up $ HNext Up $ ap "pe"), 22, Unsat)
  , (("Many nexts sat, weak", Next $ Next $ Next $ WHNext Up $ WHNext Up $ WHNext Up $ WHNext Up $ ap "pe"), 22, Sat)
  , (("HUntil equal", HUntil Up T $ ap "call"), 22, Unsat)
  , (("HRelease equal", HRelease Up T $ ap "call"), 22, Sat)
  , (("HUntil sat, trivial", Next $ Next $ Next $ HUntil Up T $ ap "pb"), 22, Sat)
  , (("HRelease sat, trivial", Next $ Next $ Next $ HRelease Up T $ ap "pb"), 22, Sat)
  , (("HUntil sat", Next $ Next $ Next $ HUntil Up T $ ap "pe"), 22, Sat)
  , (("HRelease sat", Next $ Next $ Next $ HRelease Up (ap "pe") T), 22, Sat)
  , (("HUntil unsat", Next $ Next $ Next $ HUntil Up (Not $ ap "pc") $ ap "pe"), 22, Unsat)
  , (("HRelease unsat", Next $ Next $ Next $ HRelease Up (Not $ ap "pc") $ ap "pe"), 22, Unsat)
  , (("HUntil HNext rhs sat", Next $ Next $ Next $ HUntil Up T $ HNext Up $ ap "pe"), 22, Sat)
  , (("HRelease WHNext lhs sat", Next $ Next $ Next $ HRelease Up (WHNext Up $ ap "pe") T), 22, Sat)
  , (("HUntil HNext lhs sat", Next $ Next $ Next $ HUntil Up (HNext Up $ Not $ ap "pb") $ ap "pe"), 22, Sat)
  , (("Nested HUntil sat", Next $ Next $ Next $ HUntil Up T $ HUntil Up (Not $ ap "pc") $ ap "pe"), 22, Sat)
  , (("Nested HRelease sat", Next $ Next $ Next $ HRelease Up (HRelease Up (ap "pe") (Not $ ap "pc")) T), 22, Sat)
  ]

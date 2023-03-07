module TestZ3MC ( tests ) where

import TestZ3Sat (isSupported)
import TestMP hiding (tests)
import EvalFormulas (TestCase, zipExpected, formulas)
import Pomc.Z3Encoding (modelCheckProgram, SMTResult(..), SMTStatus(..))
import Pomc.MiniProcParse (programP)

import Test.Tasty
import Test.Tasty.HUnit
import Text.Megaparsec
import qualified Data.Text as T
import Data.Maybe (fromJust)

import qualified Debug.Trace as DBG

tests :: TestTree
tests = testGroup "Z3Encoding Model Checking Tests"
  [ sasEvalTests ]

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

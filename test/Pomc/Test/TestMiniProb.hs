{-# LANGUAGE QuasiQuotes #-}
{- |
   Module      : Pomc.Test.TestMiniProp
   Copyright   : 2021-23 Michele Chiari
   License     : MIT
   Maintainer  : Michele Chiari
-}

module Pomc.Test.TestMiniProb (tests) where

import Pomc.Parse.Parser (checkRequestP, CheckRequest(..))
import Pomc.Prob.ProbUtils (Solver(..), TermQuery(..), TermResult(..))
import Pomc.Prob.ProbModelChecker (programTermination)

import Test.Tasty
import Test.Tasty.HUnit
-- import Test.Tasty.Bench
import Text.Megaparsec
import Text.RawString.QQ
import qualified Data.Text as T
import Data.Ratio ((%))

-- import qualified Debug.Trace as DBG

tests :: TestTree
tests = testGroup "MiniProb Tests" [basicTests]

makeParseTestCase :: T.Text -> (String, String, TermQuery, TermResult) -> TestTree
makeParseTestCase progSource npe@(_, phi, _, _) = testCase tname $ tthunk phi
  where (tname, tthunk) = makeParseTest progSource npe

makeParseTest :: T.Text -> (String, String, TermQuery, TermResult)
              -> (String, String -> Assertion)
makeParseTest progSource (name, phi, tquery, expected) =
  (name ++ " (" ++ phi ++ ")", assertion)
  where
    filecont f = T.concat [ T.pack "formulas = "
                          , T.pack f
                          , T.pack ";\nprogram:\n"
                          , progSource
                          ]
    assertion f = do
      pcreq <- case parse (checkRequestP <* eof) name $ filecont f of
                 Left  errBundle -> assertFailure (errorBundlePretty errBundle)
                 Right pcreq     -> return pcreq
      (tres, _) <- programTermination (pcreqMiniProc pcreq) tquery
      tres @?= expected

basicTests :: TestTree
basicTests = testGroup "Basic Tests"
  $ [ makeParseTestCase linRecSrc ("Linearly Recursive Function Termination", "F T", ApproxSingleQuery SMTWithHints, ApproxSingleResult 1)
    , makeParseTestCase randomWalkSrc ("1D Random Walk Termination", "F T", ApproxSingleQuery SMTWithHints, ApproxSingleResult (2 % 3))
    , makeParseTestCase mutualRecSrc ("Mutual Recursion Termination", "F T", ApproxSingleQuery SMTWithHints, ApproxSingleResult 1)
    ]

linRecSrc :: T.Text
linRecSrc = T.pack [r|
f() {
  bool x;
  x = 0u1 {0.5} 1u1;
  if (x) {
    f();
  } else { }
}
|]

randomWalkSrc :: T.Text
randomWalkSrc = T.pack [r|
f() {
  bool x;
  x = 0u1 {0.4} 1u1;
  if (x) {
    f();
    f();
  } else { }
}
|]

mutualRecSrc :: T.Text
mutualRecSrc = T.pack [r|
f() {
  u2 x;
  x = 0u2 {0.3} 1u2 {0.3} 2u2;
  if (x == 0u2) {
    f();
  } else {
    if (x == 1u2) {
      g();
    } else { }
  }
}

g() {
  bool x;
  x = true {0.5} false;
  if (x) {
    f();
  } else {
    g();
  }
}
|]

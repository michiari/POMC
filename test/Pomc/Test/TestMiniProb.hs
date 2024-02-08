{-# LANGUAGE QuasiQuotes #-}
{- |
   Module      : Pomc.Test.TestMiniProp
   Copyright   : 2021-24 Michele Chiari
   License     : MIT
   Maintainer  : Michele Chiari
-}

module Pomc.Test.TestMiniProb (tests) where

import Pomc.Test.EvalFormulas (excludeIndices)
import Pomc.Test.TestProbTermination (checkApproxResult)
import Pomc.Parse.Parser (checkRequestP, CheckRequest(..))
import Pomc.Prob.ProbUtils (Solver(..), TermResult(..))
import Pomc.Prob.ProbModelChecker (programTermination)
import Pomc.Prob.ProbUtils (Prob)

import Test.Tasty
import Test.Tasty.HUnit
-- import Test.Tasty.Bench
import Text.Megaparsec
import Text.RawString.QQ
import qualified Data.Text as T
import Data.Ratio ((%))

-- import qualified Debug.Trace as DBG

tests :: TestTree
tests = testGroup "MiniProb Tests" [basicSMTWithHintsTests, basicOVITests]

makeParseTestCase :: T.Text -> (String, String, Solver, Prob) -> TestTree
makeParseTestCase progSource npe@(_, phi, _, _) = testCase tname $ tthunk phi
  where (tname, tthunk) = makeParseTest progSource npe

makeParseTest :: T.Text -> (String, String, Solver, Prob)
              -> (String, String -> Assertion)
makeParseTest progSource (name, phi, solver, expected) =
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
      (ApproxSingleResult tres, _, dbginfo) <- programTermination solver (pcreqMiniProc pcreq)
      assertBool dbginfo (tres `checkApproxResult` expected)

basicSMTWithHintsTests :: TestTree
basicSMTWithHintsTests = testGroup "Basic SMTWithHints Tests"
  $ excludeIndices (basicTestCases SMTWithHints) [8]

basicOVITests :: TestTree
basicOVITests = testGroup "Basic OVI Tests" $ basicTestCases OVI

basicTestCases :: Solver -> [TestTree]
basicTestCases solver =
  [ makeParseTestCase linRecSrc ("Linearly Recursive Function Termination", "F T", solver, 1)
  , makeParseTestCase randomWalkSrc ("1D Random Walk Termination", "F T", solver, (2 % 3))
  , makeParseTestCase mutualRecSrc ("Mutual Recursion Termination", "F T", solver, 1)
  , makeParseTestCase infiniteLoopSrc ("Infinite Loop", "F T", solver, 1)
  , makeParseTestCase observeLoopSrc ("Observe Loop", "F T", solver, 1)
  , makeParseTestCase queryBugSrc ("Query Bug", "F T", solver, 0)
  , makeParseTestCase callRetLoopSrc ("Call-ret Loop", "F T", solver,  1 % 2)
  , makeParseTestCase callRet1LoopSrc ("Call-ret One Loop", "F T", solver, 2 % 3)
  , makeParseTestCase doubleRndWalkSrc ("Double random walk example", "F T", solver, 1 % 2)
  , makeParseTestCase rndWalkFunSrc ("Random walk with function call", "F T", solver, 1 % 2)
  , makeParseTestCase loopFunSrc ("Recursive loop with function call", "F T", solver, 1 % 2)
  ]

linRecSrc :: T.Text
linRecSrc = T.pack [r|
f() {
  bool x;
  x = 0u1 {1u3:2u3} 1u1;
  if (x) {
    f();
  } else { }
}
|]

randomWalkSrc :: T.Text
randomWalkSrc = T.pack [r|
f() {
  bool x;
  x = 0u1 {2u3:5u3} 1u1;
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
  x = 0u2 {1u3:3u3} 1u2 {1u3:3u3} 2u2;
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
  x = true {1u3:2u3} false;
  if (x) {
    f();
  } else {
    g();
  }
}
|]

infiniteLoopSrc :: T.Text
infiniteLoopSrc = T.pack [r|
f() {
  bool x;
  x = true;
  while (x) {
    x = true {1u3:2u3} false;
  }
}
|]

observeLoopSrc :: T.Text
observeLoopSrc = T.pack [r|
f() {
  query g();
}

g() {
  bool x;
  x = true {1u3:2u3} false;
  observe x;
}
|]

queryBugSrc :: T.Text
queryBugSrc = T.pack [r|
fun() {
  bool asd,x,y;
  query alice(x);
  query bob(y);
}

alice(bool &x) {
  bool bob_choice;
  x = true;
  query bob(bob_choice);
  observe false;
}

bob(bool &y1) { }
|]

callRetLoopSrc :: T.Text
callRetLoopSrc = T.pack [r|
pA() {
  bool x, y;
  x = true {2u4 : 3u4} false;
  while (x) {
    y = true {1u4 : 2u4} false;
    if (y) {
      pA();
    } else {
      pB();
    }
    x = true {2u4 : 3u4} false;
  }
}

pB() {
  bool x, y;
  x = true {2u4 : 3u4} false;
  while (x) {
    y = true {1u4 : 2u4} false;
    if (y) {
      pA();
    } else {
      pB();
    }
    x = true {2u4 : 3u4} false;
  }
}
|]

callRet1LoopSrc :: T.Text
callRet1LoopSrc = T.pack [r|
pA() {
  bool x, y;
  x = true {2u4 : 3u4} false;
  while (x) {
    y = true {1u4 : 2u4} false;
    if (y) {
      pA();
    } else {
      pB();
    }
  x = true {2u4 : 3u4} false;
  }
}

pB() {
  bool x, y;
  x = true {2u4 : 3u4} false;
  if (x) {
    y = true {1u4 : 2u4} false;
    if (y) {
      pA();
    } else {
      pB();
    }
  } else {}
}
|]

doubleRndWalkSrc :: T.Text
doubleRndWalkSrc = T.pack [r|
pA() {
  bool x, y;
  x = true {2u4 : 3u4} false;
  if (x) {
    y = true {1u4 : 2u4} false;
    if (y) {
      pA();
    } else {
      pB();
    }
    y = true {1u4 : 2u4} false;
    if (y) {
      pA();
    } else {
      pB();
    }
  } else {}
}

pB() {
  bool x, y;
  x = true {2u4 : 3u4} false;
  if (x) {
    y = true {1u4 : 2u4} false;
    if (y) {
      pA();
    } else {
      pB();
    }
    y = true {1u4 : 2u4} false;
    if (y) {
      pA();
    } else {
      pB();
    }
  } else {}
}
|]


rndWalkFunSrc :: T.Text
rndWalkFunSrc = T.pack [r|
pA() {
  bool x, y;
  x = true {2u4 : 3u4} false;
  if (x) {
    pA();

    y = true {1u4 : 2u4} false;
    if (y) {
      pB();
    } else { }

    pA();
  } else {}
}

pB() { }
|]


loopFunSrc :: T.Text
loopFunSrc = T.pack [r|
pA() {
  bool x;
  x = true {2u4 : 3u4} false;
  while (x) {
    pA();
    x = true {2u4 : 3u4} false;
  }
}

pB() { }
|]

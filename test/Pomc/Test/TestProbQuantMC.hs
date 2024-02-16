{- |
   Module      : Pomc.Test.TestProbQuantMC
   Copyright   : 2023 Francesco Pontiggia
   License     : MIT
   Maintainer  : Francesco Pontiggia
-}

module Pomc.Test.TestProbQuantMC (tests) where

import Test.Tasty
import Test.Tasty.HUnit
import Pomc.Test.EvalFormulas (TestCase, zipExpected, excludeIndices, probFormulas)
import Pomc.Test.TestProbTermination (checkApproxResult)
import Pomc.Test.OPMs (stlV3Alphabet, makeInputSet)
import Data.Maybe (fromJust, isJust)
import Pomc.Prob.ProbModelChecker (ExplicitPopa(..), quantitativeModelCheckExplicitGen)
import Pomc.Prob.ProbUtils (Solver(..))
import Pomc.LogUtils (selectLogVerbosity)


-- import the models
import Pomc.Test.TestProbQualMC (symmetricRandomWalk
                                , symmetricRandomWalk2
                                , biasedRandomWalk
                                , nonTerminating
                                , maybeTerminating
                                , loopySampling
                                )

import Data.Ratio((%))

type Prob = Rational

tests :: TestTree
tests = testGroup "ProbModelChecking.hs Quantitative Tests" $
  [ testGroup "ProbModelChecking.hs Quantitative Tests ExactSMTWithHints" $
    [ nonTerminatingTests OVI, loopySamplingTests OVI
    --, symmetricRandomWalkTests ExactSMTWithHints
    ]
  ]

makeTestCase :: ExplicitPopa Word String
  -> Solver
  -> (TestCase, Prob)
  -> TestTree
makeTestCase popa solv ((name, phi), expected) =
  testCase (name ++ " (" ++ show phi ++ ")") $ do
    (res, _, info) <- selectLogVerbosity Nothing $ quantitativeModelCheckExplicitGen solv phi popa
    let debugMsg = "Expected " ++ show expected ++ " but got " ++ show res ++ ". Additional diagnostic information: " ++ info
    assertBool debugMsg (checkApproxResult res expected)

-- symmetric Random Walk
symmetricRandomWalkTests :: Solver -> TestTree
symmetricRandomWalkTests solv = testGroup "Symmetric Random Walk Tests" $
  map (makeTestCase symmetricRandomWalk solv) (zipExpected probFormulas expectedSymmetricRandomWalk)

expectedSymmetricRandomWalk :: [Prob]
expectedSymmetricRandomWalk = [ 1, 1, 1, 1,
                                1, 1, 1, 0,
                                0, 1, 0, 1,
                                1, 0, 0, 1,
                                0, 1, 1
                              ]


-- a non terminating POPA
nonTerminatingTests :: Solver -> TestTree
nonTerminatingTests solv = testGroup "Non terminating POPA Tests" $
  map (makeTestCase nonTerminating solv) (zipExpected probFormulas expectedNonTerminating)


expectedNonTerminating :: [Prob]
expectedNonTerminating = [ 1, 0, 0, 0,
                           0, 1, 1, 0,
                           0, 0, 0, 0,
                           1, 0, 1, 0,
                           1, 0, 1
                         ]

maybeTerminatingTests :: Solver -> TestTree
maybeTerminatingTests solv = testGroup "Maybe terminating POPA Tests" $
  map (makeTestCase maybeTerminating solv) (zipExpected probFormulas expectedMaybeTerminating)

expectedMaybeTerminating :: [Prob]
expectedMaybeTerminating = [ 0.25, 0, 0.75, 0,
                             0,    0,    1, 0.50,
                             0.50, 0.50, 0.75, 1,
                             0.75, 1, 0.50, 0.50,
                             0.50, 1, 0.50
                           ]

-- a POPA that keeps sampling between X and Y
loopySamplingTests :: Solver -> TestTree
loopySamplingTests solv = testGroup "Loopy Sampling POPA Tests" $
  map (makeTestCase loopySampling solv) (zipExpected probFormulas expectedLoopySampling)

expectedLoopySampling :: [Prob]
expectedLoopySampling = [ 1, 1, 1, 0,
                          0, 0, 1, 0,
                          0, 0, 0, 1,
                          1, 1, 1, 1,
                          0, 1, 1
                        ]

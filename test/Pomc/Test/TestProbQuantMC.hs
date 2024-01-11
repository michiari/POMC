{- |
   Module      : Pomc.Test.TestProbQuantMC
   Copyright   : 2023 Francesco Pontiggia
   License     : MIT
   Maintainer  : Francesco Pontiggia
-}

module Pomc.Test.TestProbQuantMC(tests) where

import Test.Tasty
import Test.Tasty.HUnit
import Pomc.Test.EvalFormulas (TestCase, zipExpected, excludeIndices, probFormulas)
import Pomc.Test.OPMs (stlV3Alphabet, makeInputSet)
import Data.Maybe(fromJust, isJust)
import Pomc.Prob.ProbModelChecker (ExplicitPopa(..), quantitativeModelCheckExplicitGen)

-- import the models
import Pomc.Test.TestProbQualMC(symmetricRandomWalk
                              , symmetricRandomWalk2
                              , biasedRandomWalk
                              , nonTerminating
                              , maybeTerminating
                              , loopySampling 
                              )

import Data.Ratio((%))

type Prob = Rational

tests :: TestTree
tests = testGroup "ProbModelChecking.hs Quantitative Tests" [nonTerminatingTests, maybeTerminatingTests, loopySamplingTests]

makeTestCase :: ExplicitPopa Word String
             -> (TestCase, (Prob,Prob))
            -> TestTree
makeTestCase popa ((name, phi), (expLB, expUB)) =
  testCase (name ++ " (" ++ show phi ++ ")") $ do 
    ((lb, ub), info) <- quantitativeModelCheckExplicitGen phi popa
    let debugMsg adjective expected actual = "Expected " ++ adjective ++ show expected ++ " but got " ++ show actual ++ ". Additional diagnostic information: " ++ info
    assertBool (debugMsg "lower bound at least " expLB lb) (expLB <= lb)  
    assertBool (debugMsg "upper bound at most " expUB ub) (expUB >= ub)  
    assertBool ("Lower bound should be lower than the upper bound") (lb <= ub)  

-- symmetric Random Walk                          
symmetricRandomWalkTests :: TestTree
symmetricRandomWalkTests = testGroup "Symmetric Random Walk Tests" $
  map (makeTestCase symmetricRandomWalk) (zipExpected probFormulas expectedSymmetricRandomWalk)

expectedSymmetricRandomWalk :: [(Prob, Prob)]
expectedSymmetricRandomWalk = [ (0.99, 1.01), (0.99, 1.01), (0.99, 1.01), (0.99, 1.01), 
                                (0.99, 1.01) , (0.99, 1.01), (0.99, 1.01), (0, 0.01), 
                                (0, 0.01), (0.99, 1.01), (0, 0.01), (0.99, 1.01), 
                                (0.99, 1.01), (0, 0.01), (0, 0.01), (0.99, 1.01),
                                (0, 0.01), (0.99, 1.01), (0.99, 1.01)
                              ]


-- a non terminating POPA
nonTerminatingTests :: TestTree
nonTerminatingTests = testGroup "Non terminating POPA Tests" $
  map (makeTestCase nonTerminating) (zipExpected probFormulas expectedNonTerminating)


expectedNonTerminating :: [(Prob,Prob)]
expectedNonTerminating = [ (0.99, 1.01), (0, 0.01), (0, 0.01), (0, 0.01), 
                           (0, 0.01), (0.99, 1.01), (0.99, 1.01), (0, 0.01), 
                           (0, 0.01), (0, 0.01), (0, 0.01), (0, 0.01), 
                           (0.99, 1.01), (0, 0.01), (0.99, 1.01), (0, 0.01),
                           (0.99, 1.01), (0, 0.01), (0.99, 1.01)
                         ]

maybeTerminatingTests :: TestTree
maybeTerminatingTests = testGroup "Maybe terminating POPA Tests" $
  map (makeTestCase maybeTerminating) (zipExpected probFormulas expectedMaybeTerminating)

expectedMaybeTerminating :: [(Prob, Prob)]
expectedMaybeTerminating = [ (0.24 :: Prob, 0.26 :: Prob ) ,(0 :: Prob, 0.01 :: Prob ), (0.74 :: Prob, 0.76 :: Prob ), (0 :: Prob, 0.01 :: Prob ), 
                             (0    :: Prob, 0.01 :: Prob ), (0 :: Prob, 0.01 :: Prob ), (0.99 :: Prob, 1.01 :: Prob ), (0.49 :: Prob, 0.51 :: Prob ), 
                             (0.49 :: Prob, 0.51 :: Prob ), (0.49 :: Prob, 0.51 :: Prob ), (0.74 :: Prob, 0.76 :: Prob ), (0.99 :: Prob, 1.01 :: Prob ), 
                             (0.74 :: Prob, 0.76 :: Prob ), (0.99 :: Prob, 1.01 :: Prob ), (0.49 :: Prob, 0.51 :: Prob ), (0.49 :: Prob, 0.51 :: Prob ),
                             (0.49 :: Prob, 0.51 :: Prob ), (0.99 :: Prob, 1.01 :: Prob ), (0.49 :: Prob, 0.51 :: Prob )
                           ]

-- a POPA that keeps sampling between X and Y
loopySamplingTests :: TestTree
loopySamplingTests = testGroup "Loopy Sampling POPA Tests" $
  map (makeTestCase loopySampling) (zipExpected probFormulas expectedLoopySampling)

expectedLoopySampling :: [(Prob, Prob)]
expectedLoopySampling = [ (0.99, 1.01), (0.99, 1.01), (0.99, 1.01), (0.00, 0.01), 
                          (0.00, 0.01),  (0.00, 0.01), (0.99, 1.01), (0.00, 0.01), 
                          (0.00, 0.01), (0.00, 0.01), (0.00, 0.01), (0.99, 1.01), 
                          (0.99, 1.01), (0.99, 1.01), (0.99, 1.01), (0.99, 1.01), 
                          (0.00, 0.01), (0.99, 1.01), (0.99, 1.01)
                        ]

                
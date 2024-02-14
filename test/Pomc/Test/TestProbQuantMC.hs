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
import Pomc.Prob.ProbUtils(Solver(..))


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
tests = testGroup "ProbModelChecking.hs Quantitative Tests" $
  [ testGroup "ProbModelChecking.hs Quantitative Tests ExactSMTWithHints" $
    [ nonTerminatingTests OVI, loopySamplingTests OVI
    --, symmetricRandomWalkTests ExactSMTWithHints
    ]
  ]



makeTestCase :: ExplicitPopa Word String
  -> Solver
  -> (TestCase, (Prob,Prob))
  -> TestTree
makeTestCase popa solv ((name, phi), (expLB, expUB)) =
  testCase (name ++ " (" ++ show phi ++ ")") $ do 
    ((lb, ub), _, info) <- quantitativeModelCheckExplicitGen solv phi popa
    let debugMsg adjective expected actual = "Expected " ++ adjective ++ show expected ++ " but got " ++ show actual ++ ". Additional diagnostic information: " ++ info
    assertBool (debugMsg "lower bound at least " expLB lb) (expLB <= lb)  
    assertBool (debugMsg "upper bound at most " expUB ub) (expUB >= ub)  
    assertBool ("Lower bound should be lower than the upper bound") (lb <= ub)  

-- symmetric Random Walk                          
symmetricRandomWalkTests :: Solver -> TestTree
symmetricRandomWalkTests solv = testGroup "Symmetric Random Walk Tests" $
  map (makeTestCase symmetricRandomWalk solv) (zipExpected probFormulas expectedSymmetricRandomWalk)

expectedSymmetricRandomWalk :: [(Prob, Prob)]
expectedSymmetricRandomWalk = [ (0.99, 1.01), (0.99, 1.01), (0.99, 1.01), (0.99, 1.01), 
                                (0.99, 1.01) , (0.99, 1.01), (0.99, 1.01), (0, 0.01), 
                                (0, 0.01), (0.99, 1.01), (0, 0.01), (0.99, 1.01), 
                                (0.99, 1.01), (0, 0.01), (0, 0.01), (0.99, 1.01),
                                (0, 0.01), (0.99, 1.01), (0.99, 1.01)
                              ]


-- a non terminating POPA
nonTerminatingTests :: Solver -> TestTree
nonTerminatingTests solv = testGroup "Non terminating POPA Tests" $
  map (makeTestCase nonTerminating solv) (zipExpected probFormulas expectedNonTerminating)


expectedNonTerminating :: [(Prob,Prob)]
expectedNonTerminating = [ (0.99, 1.01), (0, 0.01), (0, 0.01), (0, 0.01), 
                           (0, 0.01), (0.99, 1.01), (0.99, 1.01), (0, 0.01), 
                           (0, 0.01), (0, 0.01), (0, 0.01), (0, 0.01), 
                           (0.99, 1.01), (0, 0.01), (0.99, 1.01), (0, 0.01),
                           (0.99, 1.01), (0, 0.01), (0.99, 1.01)
                         ]

maybeTerminatingTests :: Solver -> TestTree
maybeTerminatingTests solv = testGroup "Maybe terminating POPA Tests" $
  map (makeTestCase maybeTerminating solv) (zipExpected probFormulas expectedMaybeTerminating)

expectedMaybeTerminating :: [(Prob, Prob)]
expectedMaybeTerminating = [ (0.24 :: Prob, 0.26 :: Prob ) ,(0 :: Prob, 0.01 :: Prob ), (0.74 :: Prob, 0.76 :: Prob ), (0 :: Prob, 0.01 :: Prob ), 
                             (0    :: Prob, 0.01 :: Prob ), (0 :: Prob, 0.01 :: Prob ), (0.99 :: Prob, 1.01 :: Prob ), (0.49 :: Prob, 0.51 :: Prob ), 
                             (0.49 :: Prob, 0.51 :: Prob ), (0.49 :: Prob, 0.51 :: Prob ), (0.74 :: Prob, 0.76 :: Prob ), (0.99 :: Prob, 1.01 :: Prob ), 
                             (0.74 :: Prob, 0.76 :: Prob ), (0.99 :: Prob, 1.01 :: Prob ), (0.49 :: Prob, 0.51 :: Prob ), (0.49 :: Prob, 0.51 :: Prob ),
                             (0.49 :: Prob, 0.51 :: Prob ), (0.99 :: Prob, 1.01 :: Prob ), (0.49 :: Prob, 0.51 :: Prob )
                           ]

-- a POPA that keeps sampling between X and Y
loopySamplingTests :: Solver -> TestTree
loopySamplingTests solv = testGroup "Loopy Sampling POPA Tests" $
  map (makeTestCase loopySampling solv) (zipExpected probFormulas expectedLoopySampling)

expectedLoopySampling :: [(Prob, Prob)]
expectedLoopySampling = [ (0.99, 1.01), (0.99, 1.01), (0.99, 1.01), (0.00, 0.01), 
                          (0.00, 0.01),  (0.00, 0.01), (0.99, 1.01), (0.00, 0.01), 
                          (0.00, 0.01), (0.00, 0.01), (0.00, 0.01), (0.99, 1.01), 
                          (0.99, 1.01), (0.99, 1.01), (0.99, 1.01), (0.99, 1.01), 
                          (0.00, 0.01), (0.99, 1.01), (0.99, 1.01)
                        ]

                

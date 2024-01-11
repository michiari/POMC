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

import Data.Ratio((%))

type Prob = Rational

tests :: TestTree
tests = testGroup "ProbModelChecking.hs Quantitative Tests" [maybeTerminatingTests]

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

-- termination probability = 0.5
maybeTerminatingTests :: TestTree
maybeTerminatingTests = testGroup "Maybe terminating POPA Tests" $
  map (makeTestCase maybeTerminating) (zipExpected probFormulas expectedMaybeTerminating)

-- termination probability = 0
maybeTerminating :: (ExplicitPopa Word String)
maybeTerminating = ExplicitPopa
                        { epAlphabet = stlV3Alphabet
                        , epInitial = (0, makeInputSet ["call"])
                        , epopaDeltaPush =
                            [ (0, [(1, makeInputSet ["ret"],   0.5 :: Prob)])
                            , (0, [(3, makeInputSet ["stm"],   0.5 :: Prob)])
                            , (3, [(4, makeInputSet ["stm"],   0.5 :: Prob)])
                            , (3, [(6, makeInputSet ["stm"],   0.5 :: Prob)])
                            , (5, [(3, makeInputSet ["stm"],   1 :: Prob)])
                            , (7, [(7, makeInputSet ["call", "Y"],   1 :: Prob)])
                            , (10, [(10, makeInputSet ["stm"], 1 :: Prob)])

                            ]
                        , epopaDeltaShift =
                            [ (1, [(2, makeInputSet ["stm"], 1 :: Prob)])
                            ]
                        , epopaDeltaPop =
                            [ (4, 3, [(5, makeInputSet ["call", "X"], 1 :: Prob)])
                            , (6, 3, [(7, makeInputSet ["call", "Y"], 1 :: Prob)])
                            , (6, 5, [(7, makeInputSet ["call", "Y"], 1 :: Prob)])
                            , (2, 0, [(10, makeInputSet ["stm"], 1 :: Prob)])
                            , (10, 10, [(10, makeInputSet ["stm"], 1 :: Prob)])
                            ]
                        }

expectedMaybeTerminating :: [(Prob, Prob)]
expectedMaybeTerminating = [ (0.24 :: Prob, 0.26 :: Prob ) ,(0 :: Prob, 0.01 :: Prob ), (0.74 :: Prob, 0.76 :: Prob ), (0 :: Prob, 0.01 :: Prob ), 
                             (0    :: Prob, 0.01 :: Prob ), (0 :: Prob, 0.01 :: Prob ), (0.99 :: Prob, 1.01 :: Prob ), (0.49 :: Prob, 0.51 :: Prob ), 
                             (0.49 :: Prob, 0.51 :: Prob ), (0.49 :: Prob, 0.51 :: Prob ), (0.74 :: Prob, 0.76 :: Prob ), (0.99 :: Prob, 1.01 :: Prob ), 
                             (0.74 :: Prob, 0.76 :: Prob ), (0.99 :: Prob, 1.01 :: Prob ), (0.49 :: Prob, 0.51 :: Prob ), (0.49 :: Prob, 0.51 :: Prob ),
                             (0.49 :: Prob, 0.51 :: Prob ), (0.99 :: Prob, 1.01 :: Prob ), (0.49 :: Prob, 0.51 :: Prob )
                           ]
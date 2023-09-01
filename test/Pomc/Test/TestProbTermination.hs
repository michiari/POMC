{- |
   Module      : Pomc.Test.TestProbTermination
   Copyright   : 2023 Francesco Pontiggia
   License     : MIT
   Maintainer  : Francesco Pontiggia
-}

module Pomc.Test.TestProbTermination(tests) where

import Test.Tasty
import Test.Tasty.HUnit
import Pomc.Test.EvalFormulas (TestCase, ap, zipExpected, excludeIndices, formulas)
import Pomc.Test.OPMs (stlV2Alphabet, makeInputSet)

import Pomc.Prob.ProbModelChecker (ExplicitPopa(..), terminationExplicit)

tests :: TestTree
tests = testGroup "ProbModelChecking.hs Termination Tests" [ dummyTest]

dummyTest :: TestTree
dummyTest= testCase "Random Walk over the Stack" $ do 
    terminationExplicit example (0 :: Double)  >>= \mbSol ->
        case mbSol of
             Nothing  -> assertBool  "No solution found." $ False
             Just sol -> assertBool  ("Solution: " ++ show ((fromRational sol) :: Double)) $ False
    

-- State encoding:
-- M0 = 0, F0 = 1, F1 = 2, F2 = 3, M1 = 4,
pseudoRandomWalk :: ExplicitPopa Word String
pseudoRandomWalk = ExplicitPopa
            { epAlphabet = stlV2Alphabet
            , epInitial = (0, makeInputSet ["call"])
            , epopaDeltaPush =
                [ (0, [(0, makeInputSet ["call"], 0.5 :: Double), (1, makeInputSet ["ret"], 0.5 :: Double)])
                ]
            , epopaDeltaShift =
                [ (1, [(2, makeInputSet ["ret"], 1 :: Double)]),
                  (3, [(2, makeInputSet ["ret"], 1 :: Double)])
                ]
            , epopaDeltaPop =
                [ (2, 1, [(3, makeInputSet ["ret"], 1 :: Double)]),
                  (2, 0, [(4, makeInputSet ["ret"], 1 :: Double)])
                ]
            }

example :: ExplicitPopa Word String
example = ExplicitPopa
            { epAlphabet = stlV2Alphabet
            , epInitial = (0, makeInputSet ["call"])
            , epopaDeltaPush =
                [ (0, [(1, makeInputSet ["ret"], 1 :: Double)])
                ]
            , epopaDeltaShift =
                [ (1, [(2, makeInputSet ["ret"], 1 :: Double)])
                ]
            , epopaDeltaPop =
                [ (2, 0, [(3, makeInputSet ["ret"], 1 :: Double)])
                ]
            }
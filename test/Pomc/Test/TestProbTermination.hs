{- |
   Module      : Pomc.Test.TestProbTermination
   Copyright   : 2023 Francesco Pontiggia
   License     : MIT
   Maintainer  : Francesco Pontiggia
-}

module Pomc.Test.TestProbTermination(tests) where

import Test.Tasty
import Test.Tasty.HUnit
import Pomc.Test.OPMs (stlV2Alphabet, stlV3Alphabet, makeInputSet)
import Data.Maybe(fromJust, isJust)
import Pomc.Prob.ProbModelChecker (ExplicitPopa(..), terminationExplicit)

import Data.Ratio((%))

tests :: TestTree
tests = testGroup "ProbModelChecking.hs Termination Tests" $ map makeTestCase [dummyModel, pseudoRandomWalk, symmetricRandomWalk,
                                                                                            biasedRandomWalk]

type Prob = Rational
makeTestCase :: (ExplicitPopa Word String, String, Prob)
             -> TestTree
makeTestCase (popa, name, expected) = testCase name $ do 
  (mbSol, info) <- terminationExplicit popa expected
  -- assert that a solution is found
  assertBool ("No solution found. Additional diagnostic info: " ++ info) (isJust mbSol)
  let 
    p = fromJust mbSol
    debugMsg = "Expected " ++ show expected ++ " but got " ++ show p ++ ". Additional diagnostic information: " ++ info
  -- assert that the computed termination probability is equal to the expected one.
  assertBool debugMsg (p == expected)
  --(fromJust mbSol) @?= expected 
  
dummyModel :: (ExplicitPopa Word String, String, Prob)
dummyModel = (ExplicitPopa
                { epAlphabet = stlV2Alphabet
                , epInitial = (0, makeInputSet ["call"])
                , epopaDeltaPush =
                    [ (0, [(1, makeInputSet ["ret"], 1 :: Prob)])
                    ]
                , epopaDeltaShift =
                    [ (1, [(2, makeInputSet ["ret"], 1 :: Prob)])
                    ]
                , epopaDeltaPop =
                    [ (2, 0, [(3, makeInputSet ["ret"], 1 :: Prob)])
                    ]
                }
              , "Dummy model"
              ,  1 :: Prob 
              )

pseudoRandomWalk :: (ExplicitPopa Word String, String, Prob)
pseudoRandomWalk = (ExplicitPopa
                      { epAlphabet = stlV2Alphabet
                      , epInitial = (0, makeInputSet ["call"])
                      , epopaDeltaPush =
                          [ (0, [(0, makeInputSet ["call"], 0.5 :: Prob), (1, makeInputSet ["ret"], 0.5 :: Prob)])
                          ]
                      , epopaDeltaShift =
                          [ (1, [(2, makeInputSet ["ret"], 1 :: Prob)]),
                            (3, [(2, makeInputSet ["ret"], 1 :: Prob)])
                          ]
                      , epopaDeltaPop =
                          [ (2, 0, [(3, makeInputSet ["ret"], 1 :: Prob)])
                          ]
                      }
                    , "Pseudo Random Walk with a single recursive call"
                    , 1 :: Prob
                    )

symmetricRandomWalk :: (ExplicitPopa Word String, String, Prob)
symmetricRandomWalk = (ExplicitPopa
                        { epAlphabet = stlV2Alphabet
                        , epInitial = (0, makeInputSet ["call"])
                        , epopaDeltaPush =
                            [ (0, [(1, makeInputSet ["call"], 1 :: Prob)]),
                              (1, [(2, makeInputSet ["ret"], 1 :: Prob)]),
                              (6, [(1, makeInputSet ["call"], 1 :: Prob)]),
                              (8, [(1, makeInputSet ["call"], 1 :: Prob)])
                            ]
                        , epopaDeltaShift =
                            [ (2, [(3, makeInputSet ["ret"], 0.5 :: Prob)]),
                              (2, [(4, makeInputSet ["ret"], 0.5 :: Prob)]),
                              (5, [(7, makeInputSet ["ret"],   1 :: Prob)]),
                              (9, [(7, makeInputSet ["ret"],   1 :: Prob)])
                            ]
                        , epopaDeltaPop =
                            [ (3, 1, [(5, makeInputSet ["ret"], 1 :: Prob)]),
                              (4, 1, [(6, makeInputSet ["call"], 1 :: Prob)]),
                              (7, 6, [(8, makeInputSet ["call"], 1 :: Prob)]),
                              (7, 8, [(9, makeInputSet ["ret"], 1 :: Prob)]),
                              (7, 0, [(10, makeInputSet ["ret"], 1 :: Prob)])
                            ]
                        }
                      , "Symmetric Random Walk - two recursive calls"
                      , 1 :: Prob
                      )

-- example 1: termination probability = 2/3
biasedRandomWalk :: (ExplicitPopa Word String, String, Prob)
biasedRandomWalk = (ExplicitPopa
                      { epAlphabet = stlV3Alphabet
                      , epInitial = (0, makeInputSet ["call"])
                      , epopaDeltaPush =
                        [ (0, [(1, makeInputSet ["stm"],  1 :: Prob)]),
                          (1, [(2, makeInputSet ["stm"],  0.6 :: Prob)]),
                          (1, [(3, makeInputSet ["stm"],  0.4 :: Prob)]),
                          (4, [(1, makeInputSet ["stm"],  1 :: Prob)])
                        ]
                      , epopaDeltaShift =
                        [ (5, [(6, makeInputSet ["stm"],  1 :: Prob)])
                        ]
                      , epopaDeltaPop =
                        [ (2, 1, [(4, makeInputSet ["call"], 1 :: Prob)]),
                          (3, 1, [(5, makeInputSet ["ret"], 1 :: Prob)]),
                          (6, 4, [(1, makeInputSet ["stm"], 1 :: Prob)]),
                          (6, 0, [(7, makeInputSet ["ret"], 1 :: Prob)])  
                        ] 

                      } 
                   , "Biased Random Walk - p = 0.6"
                   , 2 % 3 :: Prob
                   )

              


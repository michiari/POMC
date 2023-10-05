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
import Pomc.Prob.ProbModelChecker (ExplicitPopa(..), terminationLTExplicit, terminationLEExplicit, terminationGTExplicit, terminationGEExplicit,
                                  terminationApproxExplicit)

import Data.Ratio((%))

tests :: TestTree
tests = testGroup "ProbModelChecking.hs Termination Tests" $ 
            [ testGroup "Boolean Termination Tests" [dummyModelTests, pseudoRandomWalkTests, symmetricRandomWalkTests,
                                                     biasedRandomWalkTests, nestedRandomWalkTests]
            , testGroup "Estimating Termination Probabilities" 
                $ map (\(popa, expected, s) -> makeTestCase popa ((s, terminationApproxExplicit), expected)) exactTerminationProbabilities
            ]

type Prob = Rational
type TestCase a = (String, (ExplicitPopa Word String -> IO (a, String)))

termQueries :: [TestCase Bool]
termQueries = [(s ++ show b, \popa -> f popa b) | (s,f) <- termFunctions, b <- termBounds]
  where termFunctions = [("LT ", terminationLTExplicit), ("LE ", terminationLEExplicit), ("GT ", terminationGTExplicit), ("GE ", terminationGEExplicit)]
        termBounds = [0.0, 0.5, 1.0]

exactTerminationProbabilities :: [(ExplicitPopa Word String, Prob, String)]
exactTerminationProbabilities = [(dummyModel, 1, "Dummy Model"), 
                                 (pseudoRandomWalk, 1, "Pseudo Random Walk"), 
                                 (symmetricRandomWalk, 1, "Symmetric Random Walk"),
                                 (biasedRandomWalk, 2%3, "Biased Random Walk"), 
                                 (nestedRandomWalk, 1%2, "Nested Random Walk")]

makeTestCase :: (Eq a, Show a)
             => (ExplicitPopa Word String)
             -> (TestCase a, a)
             -> TestTree
makeTestCase popa ((name, query), expected) = testCase name $ do 
  (res, info) <- query popa
  let debugMsg = "Expected " ++ show expected ++ " but got " ++ show res ++ ". Additional diagnostic information: " ++ info
  assertBool debugMsg (res == expected)

dummyModelTests :: TestTree
dummyModelTests = testGroup "Dummy Model Tests" $
  map (makeTestCase dummyModel) (zip termQueries expectedDummyModel)
  
-- termination probability = 1
dummyModel :: (ExplicitPopa Word String)
dummyModel = ExplicitPopa
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


expectedDummyModel :: [Bool]
expectedDummyModel = [False, False, False,
                      False, False, True,
                      True, True, False,
                      True, True, True
                      ]

pseudoRandomWalkTests :: TestTree
pseudoRandomWalkTests = testGroup "Pseudo Random Walk Tests" $
  map (makeTestCase pseudoRandomWalk) (zip termQueries expectedPseudoRandomWalk)

-- termination probability = 1
pseudoRandomWalk :: (ExplicitPopa Word String)
pseudoRandomWalk = ExplicitPopa
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

expectedPseudoRandomWalk :: [Bool]
expectedPseudoRandomWalk = [False, False, False,
                            False, False, True,
                            True, True, False,
                            True, True, True
                           ]

symmetricRandomWalkTests :: TestTree
symmetricRandomWalkTests = testGroup "Symmetric Random Walk Tests" $
  map (makeTestCase symmetricRandomWalk) (zip termQueries expectedSymmetricRandomWalk)

-- termination probability = 1
symmetricRandomWalk :: (ExplicitPopa Word String)
symmetricRandomWalk = ExplicitPopa
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

expectedSymmetricRandomWalk :: [Bool]
expectedSymmetricRandomWalk = [ False, False, False,
                                False, False, True,
                                True, True, False,
                                True, True, True
                              ]

biasedRandomWalkTests :: TestTree
biasedRandomWalkTests = testGroup "Biased Random Walk Tests" $
  map (makeTestCase biasedRandomWalk) (zip termQueries expectedBiasedRandomWalk)

-- example 1: termination probability = 2/3
biasedRandomWalk :: (ExplicitPopa Word String)
biasedRandomWalk = ExplicitPopa
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

expectedBiasedRandomWalk :: [Bool]
expectedBiasedRandomWalk = [ False, False, True, 
                             False, False, True,
                             True, True, False,
                             True, True, False
                           ]


nestedRandomWalkTests :: TestTree
nestedRandomWalkTests = testGroup "Nested Random WalkTests" $
  map (makeTestCase nestedRandomWalk) (zip termQueries expectedNestedRandomWalk)

-- termination probability = 0.5?
nestedRandomWalk :: (ExplicitPopa Word String)
nestedRandomWalk = ExplicitPopa
                        { epAlphabet = stlV3Alphabet
                        , epInitial = (0, makeInputSet ["call"])
                        , epopaDeltaPush =
                            [ (0, [(1, makeInputSet ["stm"],   1 :: Prob)]),
                              (1, [(2, makeInputSet ["stm"], 0.5 :: Prob)]),
                              (1, [(3, makeInputSet ["stm"], 0.5 :: Prob)]),
                              (4, [(5, makeInputSet ["stm"],   1 :: Prob)]),
                              (5, [(6, makeInputSet ["stm"], 0.5 :: Prob)]),
                              (5, [(7, makeInputSet ["stm"], 0.5 :: Prob)]),
                              (8, [(5, makeInputSet ["stm"],   1 :: Prob)]),
                              (9, [(1, makeInputSet ["stm"],   1 :: Prob)])
                            ]
                        , epopaDeltaShift =
                            [ (10, [(11, makeInputSet ["stm"], 1 :: Prob)]),
                              (13, [(14, makeInputSet ["stm"], 1 :: Prob)])
                            ]
                        , epopaDeltaPop =
                            [ (2, 1, [(4, makeInputSet ["call"], 1 :: Prob)]),
                              (6, 5, [(8, makeInputSet ["call"], 1 :: Prob)]),
                              (7, 5, [(9, makeInputSet ["call"], 1 :: Prob)]),
                              (3, 1, [(10, makeInputSet ["ret"], 1 :: Prob)]),
                              (11, 0, [(12, makeInputSet ["ret"], 1 :: Prob)]),
                              (11, 9, [(13, makeInputSet ["ret"], 1 :: Prob)]),
                              (14, 8, [(9, makeInputSet ["call"], 1 :: Prob)]),
                              (14, 10, [(4, makeInputSet ["ret"], 1 :: Prob)])     
                            ]
                        }

expectedNestedRandomWalk :: [Bool]
expectedNestedRandomWalk = [ False, False, True,
                             False, True, True,
                             True, False, False,
                             True, True, False
                            ]
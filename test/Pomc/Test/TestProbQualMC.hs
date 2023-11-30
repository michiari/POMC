{- |
   Module      : Pomc.Test.TestProbQualMC
   Copyright   : 2023 Francesco Pontiggia
   License     : MIT
   Maintainer  : Francesco Pontiggia
-}

module Pomc.Test.TestProbQualMC(tests) where

import Test.Tasty
import Test.Tasty.HUnit
import Pomc.Test.EvalFormulas (TestCase, ap, zipExpected, excludeIndices, probFormulas)
import Pomc.Test.OPMs (stlV3Alphabet, makeInputSet)
import Data.Maybe(fromJust, isJust)
import Pomc.Potl (Formula(..), Dir(..))
import Pomc.Prob.ProbModelChecker (ExplicitPopa(..), qualitativeModelCheckExplicitGen)

import Data.Ratio((%))

tests :: TestTree
tests = testGroup "ProbModelChecking.hs Qualitative Tests" [symmetricRandomWalkTests, 
  symmetricRandomWalk2Tests
  , biasedRandomWalkTests, nonTerminatingTests, maybeTerminatingTests
  , loopySamplingTests
  ]

type Prob = Rational

makeTestCase :: ExplicitPopa Word String
             -> (TestCase, Bool)
            -> TestTree
makeTestCase popa ((name, phi), expected) =
  testCase (name ++ " (" ++ show phi ++ ")") $ do 
    (res, info) <- qualitativeModelCheckExplicitGen phi popa
    let debugMsg = "Expected " ++ show expected ++ " but got " ++ show res ++ ". Additional diagnostic information: " ++ info
    assertBool debugMsg (res == expected)  
  
-- symmetric Random Walk                          
symmetricRandomWalkTests :: TestTree
symmetricRandomWalkTests = testGroup "Symmetric Random Walk Tests" $
  map (makeTestCase symmetricRandomWalk) (zipExpected probFormulas expectedSymmetricRandomWalk)

-- termination probability = 1
symmetricRandomWalk :: (ExplicitPopa Word String)
symmetricRandomWalk = ExplicitPopa
                        { epAlphabet = stlV3Alphabet
                        , epInitial = (0, makeInputSet ["call"])
                        , epopaDeltaPush =
                            [ (0, [(1, makeInputSet ["call"], 1 :: Prob)])
                            , (1, [(2, makeInputSet ["ret"], 1 :: Prob)])
                            , (6, [(1, makeInputSet ["call"], 1 :: Prob)])
                            , (8, [(1, makeInputSet ["call"], 1 :: Prob)])
                            , (10, [(10, makeInputSet ["stm"], 1 :: Prob)])
                            ]
                        , epopaDeltaShift =
                            [ (2, [(3, makeInputSet ["ret"], 0.5 :: Prob)])
                            , (2, [(4, makeInputSet ["ret"], 0.5 :: Prob)])
                            , (5, [(7, makeInputSet ["stm"], 1 :: Prob)])
                            , (9, [(7, makeInputSet ["stm"], 1 :: Prob)])
                            ]
                        , epopaDeltaPop =
                            [ (3, 1, [(5, makeInputSet ["ret", "X", "Y"], 1 :: Prob)])
                            , (4, 1, [(6, makeInputSet ["call"],          1 :: Prob)])
                            , (7, 6, [(8, makeInputSet ["call", "X"],     1 :: Prob)])
                            , (7, 8, [(9, makeInputSet ["ret", "X", "Y"], 1 :: Prob)])
                            , (7, 0, [(10, makeInputSet ["stm"],          1 :: Prob)])
                            , (10, 10, [(10, makeInputSet ["stm"],        1 :: Prob)])
                            ]
                        }

expectedSymmetricRandomWalk :: [Bool]
expectedSymmetricRandomWalk = [ True, True, True, True, True , True, True, False, False, True,
                                False, True, True, False, False
                              ]

-- secondo version of Symmetric Random Walk                         
symmetricRandomWalk2Tests :: TestTree
symmetricRandomWalk2Tests = testGroup "Symmetric Random Walk 2 Tests" $
  map (makeTestCase symmetricRandomWalk2) (zipExpected probFormulas expectedsymmetricRandomWalk2)

-- termination probability = 1
symmetricRandomWalk2 :: (ExplicitPopa Word String)
symmetricRandomWalk2 = ExplicitPopa
                      { epAlphabet = stlV3Alphabet
                      , epInitial = (0, makeInputSet ["call"])
                      , epopaDeltaPush =
                        [ (0, [(1, makeInputSet ["stm"],  1 :: Prob)])
                        , (1, [(2, makeInputSet ["stm"],  0.5 :: Prob)])
                        , (1, [(3, makeInputSet ["stm"],  0.5 :: Prob)])
                        , (4, [(1, makeInputSet ["stm"],  1 :: Prob)])
                        , (7, [(7, makeInputSet ["stm"], 1 :: Prob)])  
                        ]
                      , epopaDeltaShift =
                        [ (5, [(6, makeInputSet ["stm"],  1 :: Prob)])
                        ]
                      , epopaDeltaPop =
                        [ (2, 1, [(4, makeInputSet ["call", "X"], 1 :: Prob)])
                        , (3, 1, [(5, makeInputSet ["ret", "X", "Y"], 1 :: Prob)])
                        , (6, 4, [(1, makeInputSet ["stm"], 1 :: Prob)])
                        , (6, 0, [(7, makeInputSet ["stm"], 1 :: Prob)]) 
                        , (7, 7, [(7, makeInputSet ["stm"], 1 :: Prob)])  
                        ] 
                      } 

expectedsymmetricRandomWalk2 :: [Bool]
expectedsymmetricRandomWalk2 = [True, True, True, True, 
                                True, True, True, True, False, True,
                                False, True, True, False, False
                           ]

-- biased Random Walk (same as symmetric, but with an unfair coin flip)                          
biasedRandomWalkTests :: TestTree
biasedRandomWalkTests = testGroup "Biased Random Walk Tests" $
  map (makeTestCase biasedRandomWalk) (zipExpected probFormulas expectedBiasedRandomWalk)

-- example 1: termination probability = 2/3
biasedRandomWalk :: (ExplicitPopa Word String)
biasedRandomWalk = ExplicitPopa
                  { epAlphabet = stlV3Alphabet
                  , epInitial = (0, makeInputSet ["call"])
                  , epopaDeltaPush =
                    [ (0, [(1, makeInputSet ["stm"],  1 :: Prob)])
                    , (1, [(2, makeInputSet ["stm"],  0.6 :: Prob)])
                    , (1, [(3, makeInputSet ["stm"],  0.4 :: Prob)])
                    , (4, [(1, makeInputSet ["stm"],  1 :: Prob)])
                    , (7, [(7, makeInputSet ["stm"], 1 :: Prob)])  
                    ]
                  , epopaDeltaShift =
                    [ (5, [(6, makeInputSet ["stm"],  1 :: Prob)])
                    ]
                  , epopaDeltaPop =
                    [ (2, 1, [(4, makeInputSet ["call", "X"], 1 :: Prob)])
                    , (3, 1, [(5, makeInputSet ["ret", "X", "Y"], 1 :: Prob)])
                    , (6, 4, [(1, makeInputSet ["stm"], 1 :: Prob)])
                    , (6, 0, [(7, makeInputSet ["stm"], 1 :: Prob)]) 
                    , (7, 7, [(7, makeInputSet ["stm"], 1 :: Prob)])  
                    ] 
                  } 

expectedBiasedRandomWalk :: [Bool]
expectedBiasedRandomWalk = [True, True, False, False, False, True, True, True, False, False,
                            False, True, True, False, False
                           ]

-- a non terminating POPA
nonTerminatingTests :: TestTree
nonTerminatingTests = testGroup "Non terminating POPA Tests" $
  map (makeTestCase nonTerminating) (zipExpected probFormulas expectedNonTerminating)

-- termination probability = 0
nonTerminating :: (ExplicitPopa Word String)
nonTerminating = ExplicitPopa
                        { epAlphabet = stlV3Alphabet
                        , epInitial = (0, makeInputSet ["call"])
                        , epopaDeltaPush =
                            [ (0, [(1, makeInputSet ["call"],   1 :: Prob)]),
                              (1, [(2, makeInputSet ["call", "X"],   1 :: Prob)]),
                              (2, [(2, makeInputSet ["call", "X"],   1 :: Prob)])
                            ]
                        , epopaDeltaShift =
                            [ 
                            ]
                        , epopaDeltaPop =
                            [   
                            ]
                        }

expectedNonTerminating :: [Bool]
expectedNonTerminating = [ True, False, False, False, False, True, True, False, False, False,
                           False, False, True, False, True
                         ]

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

expectedMaybeTerminating :: [Bool]
expectedMaybeTerminating = [ False, False, False, False, False, False, True, False, False, False,
                             False, True, False, True, False
                            ]


-- a POPA that keeps sampling between X and Y
loopySamplingTests :: TestTree
loopySamplingTests = testGroup "Loopy Sampling POPA Tests" $
  map (makeTestCase loopySampling) (zipExpected probFormulas expectedLoopySampling)

-- termination probability = 0
loopySampling :: (ExplicitPopa Word String)
loopySampling = ExplicitPopa
                        { epAlphabet = stlV3Alphabet
                        , epInitial = (0, makeInputSet ["call"])
                        , epopaDeltaPush =
                            [ (0, [(1, makeInputSet ["call", "S"],   1 :: Prob)])
                            , (1, [(2, makeInputSet ["stm", "X"],   0.5 :: Prob)])
                            , (1, [(3, makeInputSet ["stm", "Y"],   0.5 :: Prob)])
                            , (2, [(4, makeInputSet ["ret", "X"],   1 :: Prob)])
                            , (3, [(5, makeInputSet ["ret", "Y"],   1 :: Prob)])

                            ]
                        , epopaDeltaShift =
                            [ (6, [(8, makeInputSet ["call", "S"],   1 :: Prob)])
                            , (7, [(8, makeInputSet ["call", "S"],   1 :: Prob)])
                            ]
                        , epopaDeltaPop =
                            [ (4, 2, [(6, makeInputSet ["ret", "X"],   1 :: Prob)])
                            , (5, 3, [(7, makeInputSet ["ret", "Y"],   1 :: Prob)])
                            , (8, 1, [(1, makeInputSet ["call", "S"],   1 :: Prob)])
                            ]
                        }

expectedLoopySampling :: [Bool]
expectedLoopySampling = [ True, True, True, False, False, False, True, False, False, False, False, True, True, True, True 
                         ]



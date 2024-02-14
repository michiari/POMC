{- |
   Module      : Pomc.Test.TestProbQualMC
   Copyright   : 2024 Francesco Pontiggia
   License     : MIT
   Maintainer  : Francesco Pontiggia
-}

module Pomc.Test.TestProbQualMC ( tests
                                , symmetricRandomWalk
                                , symmetricRandomWalk2
                                , biasedRandomWalk
                                , nonTerminating
                                , maybeTerminating
                                , loopySampling
                                ) where

import Test.Tasty
import Test.Tasty.HUnit
import Pomc.Test.EvalFormulas (TestCase, zipExpected, excludeIndices, probFormulas)
import Pomc.Test.OPMs (stlV3Alphabet, makeInputSet)
import Pomc.Prob.ProbModelChecker (ExplicitPopa(..), qualitativeModelCheckExplicitGen)
import Pomc.Prob.ProbUtils (Solver(..))

tests :: TestTree
tests = testGroup "ProbModelChecking.hs Qualitative Tests" $
  [ testGroup "ProbModelChecking.hs Qualitative Tests OVI" $
    map (\t -> t OVI) 
      [ biasedRandomWalkTests
      , nonTerminatingTests
      , maybeTerminatingTests
      , loopySamplingTests
      ]
  , testGroup "ProbModelChecking.hs Qualitative Tests SMTWithHints" $
    map (\t -> t SMTWithHints) 
      [ biasedRandomWalkTests
      , nonTerminatingTests
      , maybeTerminatingTests
      , loopySamplingTests
      ]
  , testGroup "ProbModelChecking.hs Qualitative Tests ExactSMTWithHints" $
    map (\t -> t ExactSMTWithHints) 
      [ symmetricRandomWalkTests
      , symmetricRandomWalk2Tests
      , biasedRandomWalkTests
      , nonTerminatingTests
      , maybeTerminatingTests
      , loopySamplingTests
      ]

  ]

type Prob = Rational

makeTestCase :: ExplicitPopa Word String
             -> Solver 
             -> (TestCase, Bool)
              -> TestTree
makeTestCase popa solv ((name, phi), expected) =
  testCase (name ++ " (" ++ show phi ++ ")") $ do 
    (res, _, info) <- qualitativeModelCheckExplicitGen solv phi popa
    let debugMsg = "Expected " ++ show expected ++ " but got " ++ show res ++ ". Additional diagnostic information: " ++ info
    assertBool debugMsg (res == expected)  
  
-- symmetric Random Walk                          
symmetricRandomWalkTests :: Solver -> TestTree
symmetricRandomWalkTests solv = testGroup "Symmetric Random Walk Tests" $
  map (makeTestCase symmetricRandomWalk solv) (zipExpected probFormulas expectedSymmetricRandomWalk)

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
expectedSymmetricRandomWalk = [ True, True, True, True,
                                True , True, True, False,
                                False, True, False, True,
                                True, False, False, True,
                                False, True, True
                              ]

-- second version of Symmetric Random Walk                         
symmetricRandomWalk2Tests :: Solver -> TestTree
symmetricRandomWalk2Tests solv = testGroup "Symmetric Random Walk 2 Tests" $
  map (makeTestCase symmetricRandomWalk2 solv) (zipExpected probFormulas expectedsymmetricRandomWalk2)

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
expectedsymmetricRandomWalk2 = [ True, True, True, True,
                                 True, True, True, True,
                                 False, True, False, True,
                                 True, False, False, True,
                                 False, True, True
                               ]

-- biased Random Walk (same as symmetric, but with an unfair coin flip)                          
biasedRandomWalkTests :: Solver -> TestTree
biasedRandomWalkTests solv = testGroup "Biased Random Walk Tests" $
  map (makeTestCase biasedRandomWalk solv) (zipExpected probFormulas expectedBiasedRandomWalk)

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
expectedBiasedRandomWalk = [ True, True, False, False,
                             False, True, True, True,
                             False, False, False, True,
                             True, False, False, False,
                             False, True, True
                           ]

-- a non terminating POPA
nonTerminatingTests :: Solver -> TestTree
nonTerminatingTests solv = testGroup "Non terminating POPA Tests" $
  map (makeTestCase nonTerminating solv) (zipExpected probFormulas expectedNonTerminating)

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
expectedNonTerminating = [ True, False, False, False,
                           False, True, True, False,
                           False, False, False, False,
                           True, False, True, False,
                           True, False, True
                         ]

-- termination probability = 0.5
maybeTerminatingTests :: Solver -> TestTree
maybeTerminatingTests solv = testGroup "Maybe terminating POPA Tests" $
  map (makeTestCase maybeTerminating solv) (zipExpected probFormulas expectedMaybeTerminating)

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
expectedMaybeTerminating = [ False, False, False, False,
                             False, False, True, False,
                             False, False, False, True,
                             False, True, False, False,
                             False, True, False
                           ]


-- a POPA that keeps sampling between X and Y
loopySamplingTests :: Solver -> TestTree
loopySamplingTests solv = testGroup "Loopy Sampling POPA Tests" $
  map (makeTestCase loopySampling solv) (zipExpected probFormulas expectedLoopySampling)

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
expectedLoopySampling = [ True, True, True, False,
                          False, False, True, False,
                          False, False, False, True,
                          True, True, True, True,
                          False, True, True
                        ]

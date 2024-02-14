{- |
   Module      : Pomc.Test.TestProbTermination
   Copyright   : 2024 Francesco Pontiggia and Michele Chiari
   License     : MIT
   Maintainer  : Francesco Pontiggia
-}

module Pomc.Test.TestProbTermination (tests, checkApproxResult) where

import Test.Tasty
import Test.Tasty.HUnit
import Pomc.Test.OPMs (stlV3Alphabet, makeInputSet)
import Pomc.Test.EvalFormulas (excludeIndices)
import Pomc.Prob.ProbModelChecker ( ExplicitPopa(..)
                                  , terminationLTExplicit, terminationLEExplicit
                                  , terminationGTExplicit, terminationGEExplicit
                                  , terminationApproxExplicit
                                  )

import Pomc.Prob.ProbUtils (Solver(..), Stats)
import Data.Ratio ((%))

tests :: TestTree
tests = testGroup "ProbModelChecking.hs Termination Tests" $
  [ testGroup "Boolean Termination Tests"
    [ dummyModelTests
    , pseudoRandomWalkTests
    , symmetricRandomWalkTests
    , biasedRandomWalkTests
    , nestedRandomWalkTests
    , nonTerminatingTests
    ]
  , testGroup "Estimating Termination Probabilities with OVI"
    $ flip excludeIndices [2,4]
    $ map (\(popa, expected, s) -> makeTestCase checkApproxResult popa ((s, \popa' -> terminationApproxExplicit popa' OVI), expected)) exactTerminationProbabilities
  , testGroup "Estimating Termination Probabilities with SMTWithHints"
    $ flip excludeIndices [2,4, 7, 8]
    $ map (\(popa, expected, s) -> makeTestCase checkApproxResult popa ((s, \popa' -> terminationApproxExplicit popa' SMTWithHints), expected)) exactTerminationProbabilities
  , testGroup "Computing Exact Terminating Probabilities"
    $ flip excludeIndices [6, 7, 8]
    $ map (\(popa, expected, s) -> makeTestCase checkApproxResult popa ((s, \popa' -> terminationApproxExplicit popa' ExactSMTWithHints), expected)) exactTerminationProbabilities
  ]

type Prob = Rational
type TestCase a = (String, (ExplicitPopa Word String -> IO (a, Stats, String)))

termQueries :: [TestCase Bool]
termQueries = [(s ++ show b, \popa -> f popa b ExactSMTWithHints) | (s,f) <- termFunctions, b <- termBounds]
  where termFunctions = [("LT ", terminationLTExplicit), ("LE ", terminationLEExplicit), ("GT ", terminationGTExplicit), ("GE ", terminationGEExplicit)]
        termBounds = [0.0, 0.5, 1.0]

exactTerminationProbabilities :: [(ExplicitPopa Word String, Prob, String)]
exactTerminationProbabilities =
  [ (dummyModel, 1, "Dummy Model")
  , (pseudoRandomWalk, 1, "Pseudo Random Walk")
  , (symmetricRandomWalk, 1, "Symmetric Random Walk")
  , (biasedRandomWalk, 2%3, "Biased Random Walk")
  , (nestedRandomWalk, 1, "Nested Random Walk")
  , (nonTerminating, 0, "Non terminating POPA")
  , (callRetEx, 1 % 4, "Call-ret example")
  , (callRetLoop1, 1 % 4, "Call-ret Loop 1")
  , (callRetLoop2, 0, "Call-ret Loop 2")
  , (loopFunShort, 1 % 2, "Recursive loop with function call short")
  , (loopFunStm, 1 % 2, "Recursive loop with function call and stm")
  ]

checkApproxResult :: (Ord a, Fractional a) => (a, a) -> a -> Bool
checkApproxResult (lb, ub) e = e - tol <= lb && lb <= ub && ub <= e + tol
  where tol = fromRational $ 1 % 10^(2 :: Integer)

makeTestCase :: (Show a, Show b)
             => (a -> b -> Bool)
             -> (ExplicitPopa Word String)
             -> (TestCase a, b)
             -> TestTree
makeTestCase consistent popa ((name, query), expected) = testCase name $ do
  (res, _, info) <- query popa
  let debugMsg = "Expected " ++ show expected ++ " but got " ++ show res ++ ". Additional diagnostic information: " ++ info
  assertBool debugMsg (res `consistent` expected)

-- dummy model
dummyModelTests :: TestTree
dummyModelTests = testGroup "Dummy Model Tests" $
  map (makeTestCase (==) dummyModel) (zip termQueries expectedDummyModel)

-- termination probability = 1
dummyModel :: (ExplicitPopa Word String)
dummyModel = ExplicitPopa
  { epAlphabet = stlV3Alphabet
  , epInitial = (0, makeInputSet ["call"])
  , epopaDeltaPush =
      [ (0, [(1, makeInputSet ["ret"], 1 :: Prob)]) ]
  , epopaDeltaShift =
      [ (1, [(2, makeInputSet ["ret"], 1 :: Prob)]) ]
  , epopaDeltaPop =
      [ (2, 0, [(3, makeInputSet ["ret"], 1 :: Prob)]) ]
  }

expectedDummyModel :: [Bool]
expectedDummyModel =
  [ False, False, False
  , False, False, True
  , True, True, False
  , True, True, True
  ]

-- pseudo Random Walk
pseudoRandomWalkTests :: TestTree
pseudoRandomWalkTests = testGroup "Pseudo Random Walk Tests" $
  map (makeTestCase (==) pseudoRandomWalk) (zip termQueries expectedPseudoRandomWalk)

-- termination probability = 1
pseudoRandomWalk :: (ExplicitPopa Word String)
pseudoRandomWalk = ExplicitPopa
  { epAlphabet = stlV3Alphabet
  , epInitial = (0, makeInputSet ["call"])
  , epopaDeltaPush =
      [ (0, [(0, makeInputSet ["call"], 0.5 :: Prob), (1, makeInputSet ["ret"], 0.5 :: Prob)]) ]
  , epopaDeltaShift =
      [ (1, [(2, makeInputSet ["ret"], 1 :: Prob)])
      , (3, [(2, makeInputSet ["ret"], 1 :: Prob)])
      ]
  , epopaDeltaPop =
      [ (2, 0, [(3, makeInputSet ["ret"], 1 :: Prob)]) ]
  }

expectedPseudoRandomWalk :: [Bool]
expectedPseudoRandomWalk =
  [ False, False, False
  , False, False, True
  , True, True, False
  , True, True, True
  ]

-- symmetric Random Walk
symmetricRandomWalkTests :: TestTree
symmetricRandomWalkTests = testGroup "Symmetric Random Walk Tests" $
  map (makeTestCase (==) symmetricRandomWalk) (zip termQueries expectedSymmetricRandomWalk)

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
      ]
  , epopaDeltaShift =
      [ (2, [(3, makeInputSet ["ret"], 0.5 :: Prob)])
      , (2, [(4, makeInputSet ["ret"], 0.5 :: Prob)])
      , (5, [(7, makeInputSet ["ret"],   1 :: Prob)])
      , (9, [(7, makeInputSet ["ret"],   1 :: Prob)])
      ]
  , epopaDeltaPop =
      [ (3, 1, [(5, makeInputSet ["ret"], 1 :: Prob)])
      , (4, 1, [(6, makeInputSet ["call"], 1 :: Prob)])
      , (7, 6, [(8, makeInputSet ["call"], 1 :: Prob)])
      , (7, 8, [(9, makeInputSet ["ret"], 1 :: Prob)])
      , (7, 0, [(10, makeInputSet ["ret"], 1 :: Prob)])
      ]
  }

expectedSymmetricRandomWalk :: [Bool]
expectedSymmetricRandomWalk =
  [ False, False, False
  , False, False, True
  , True, True, False
  , True, True, True
  ]

-- biased Random Walk
biasedRandomWalkTests :: TestTree
biasedRandomWalkTests = testGroup "Biased Random Walk Tests" $
  map (makeTestCase (==) biasedRandomWalk) (zip termQueries expectedBiasedRandomWalk)

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
      ]
  , epopaDeltaShift =
      [ (5, [(6, makeInputSet ["stm"],  1 :: Prob)]) ]
  , epopaDeltaPop =
      [ (2, 1, [(4, makeInputSet ["call"], 1 :: Prob)])
      , (3, 1, [(5, makeInputSet ["ret"], 1 :: Prob)])
      , (6, 4, [(1, makeInputSet ["stm"], 1 :: Prob)])
      , (6, 0, [(7, makeInputSet ["ret"], 1 :: Prob)])
      ]
  }

expectedBiasedRandomWalk :: [Bool]
expectedBiasedRandomWalk =
  [ False, False, True
  , False, False, True
  , True, True, False
  , True, True, False
  ]

-- nested Random Walk
nestedRandomWalkTests :: TestTree
nestedRandomWalkTests = testGroup "Nested Random Walk Tests" $
  map (makeTestCase (==) nestedRandomWalk) (zip termQueries expectedNestedRandomWalk)

-- termination probability = 1
nestedRandomWalk :: (ExplicitPopa Word String)
nestedRandomWalk = ExplicitPopa
  { epAlphabet = stlV3Alphabet
  , epInitial = (0, makeInputSet ["call"])
  , epopaDeltaPush =
      [ (0, [(1, makeInputSet ["stm"],   1 :: Prob)])
       , (1, [(2, makeInputSet ["stm"], 0.5 :: Prob)])
       , (1, [(3, makeInputSet ["stm"], 0.5 :: Prob)])
       , (4, [(5, makeInputSet ["stm"],   1 :: Prob)])
       , (5, [(6, makeInputSet ["stm"], 0.5 :: Prob)])
       , (5, [(7, makeInputSet ["stm"], 0.5 :: Prob)])
       , (8, [(5, makeInputSet ["stm"],   1 :: Prob)])
       , (9, [(1, makeInputSet ["stm"],   1 :: Prob)])
      ]
  , epopaDeltaShift =
      [ (10, [(11, makeInputSet ["stm"], 1 :: Prob)])
      , (13, [(14, makeInputSet ["stm"], 1 :: Prob)])
      ]
  , epopaDeltaPop =
      [ (2, 1, [(4, makeInputSet ["call"], 1 :: Prob)])
      , (6, 5, [(8, makeInputSet ["call"], 1 :: Prob)])
      , (7, 5, [(9, makeInputSet ["call"], 1 :: Prob)])
      , (3, 1, [(10, makeInputSet ["ret"], 1 :: Prob)])
      , (11, 0, [(12, makeInputSet ["ret"], 1 :: Prob)])
      , (11, 9, [(13, makeInputSet ["ret"], 1 :: Prob)])
      , (14, 8, [(9, makeInputSet ["call"], 1 :: Prob)])
      , (14, 4, [(10, makeInputSet ["ret"], 1 :: Prob)])
      ]
  }

expectedNestedRandomWalk :: [Bool]
expectedNestedRandomWalk =
  [ False, False, False
  , False, False, True
  , True, True, False
  , True, True, True
  ]

-- a non terminating POPA
nonTerminatingTests :: TestTree
nonTerminatingTests = testGroup "Non terminating POPA Tests" $
  map (makeTestCase (==) nonTerminating) (zip termQueries expectedNonTerminating)

-- termination probability = 0
nonTerminating :: (ExplicitPopa Word String)
nonTerminating = ExplicitPopa
  { epAlphabet = stlV3Alphabet
  , epInitial = (0, makeInputSet ["call"])
  , epopaDeltaPush =
      [ (0, [(1, makeInputSet ["call"],   1 :: Prob)])
      , (1, [(1, makeInputSet ["call"],   1 :: Prob)])
      ]
  , epopaDeltaShift =
      [ ]
  , epopaDeltaPop =
      [ ]
  }

expectedNonTerminating :: [Bool]
expectedNonTerminating =
  [ False, True, True
  , True, True, True
  , False, False, False
  , True, False, False
  ]

callRetExTests :: TestTree
callRetExTests = testGroup "Call-ret example Tests" $
  map (makeTestCase (==) callRetEx) (zip termQueries expectedcallRetEx)

callRetEx :: ExplicitPopa Word String
callRetEx = ExplicitPopa
  { epAlphabet = stlV3Alphabet
  , epInitial = (0, makeInputSet ["call"])
  , epopaDeltaPush =
      [ (0, [(1, makeInputSet ["call"], 1)])
      , (1, [(1, makeInputSet ["call"], 2 % 3), (2, makeInputSet ["ret"], 1 % 3)])
      ]
  , epopaDeltaShift =
      [ (2, [(1, makeInputSet ["call"], 1 :: Prob)]) ]
  , epopaDeltaPop =
      [ (1, 1, [(1, makeInputSet ["call"], 2 % 3), (2, makeInputSet ["ret"], 1 % 3)])
      , (1, 0, [(3, makeInputSet ["call"], 1)])
      ]
  }

expectedcallRetEx :: [Bool]
expectedcallRetEx =
  [ False, True, True
  , False, True, True
  , True, False, False
  , True, False, False
  ]

callRetLoop1 :: ExplicitPopa Word String
callRetLoop1 = ExplicitPopa
  { epAlphabet = stlV3Alphabet
  , epInitial = (0, makeInputSet ["call"])
  , epopaDeltaPush =
      [ (0, [(1, makeInputSet ["call"], 1)])
      , (1, [(1, makeInputSet ["call"], 1 % 3), (2, makeInputSet ["call"], 1 % 3), (3, makeInputSet ["ret"], 1 % 3)])
      , (2, [(1, makeInputSet ["call"], 1 % 3), (2, makeInputSet ["call"], 1 % 3), (3, makeInputSet ["ret"], 1 % 3)])
      , (4, [(4, makeInputSet ["stm"], 1)])
      ]
  , epopaDeltaShift =
      [ (3, [(3, makeInputSet ["ret"], 1)]) ]
  , epopaDeltaPop =
      [ (3, 1, [(1, makeInputSet ["call"], 1 % 3), (2, makeInputSet ["call"], 1 % 3), (3, makeInputSet ["ret"], 1 % 3)])
      , (3, 2, [(1, makeInputSet ["call"], 1 % 3), (2, makeInputSet ["call"], 1 % 3), (3, makeInputSet ["ret"], 1 % 3)])
      , (3, 0, [(4, makeInputSet ["stm"], 1)])
      , (4, 4, [(4, makeInputSet ["stm"], 1)])
      ]
  }

callRetLoop2 :: ExplicitPopa Word String
callRetLoop2 = ExplicitPopa
  { epAlphabet = stlV3Alphabet
  , epInitial = (0, makeInputSet ["call"])
  , epopaDeltaPush =
      [ (0, [(1, makeInputSet ["call"], 1)])
      , (1, [(1, makeInputSet ["call"], 1 % 3), (2, makeInputSet ["call"], 1 % 3), (3, makeInputSet ["ret"], 1 % 3)])
      , (2, [(1, makeInputSet ["call"], 1 % 3), (2, makeInputSet ["call"], 1 % 3), (3, makeInputSet ["ret"], 1 % 3)])
      ]
  , epopaDeltaShift =
      [ (3, [(1, makeInputSet ["call"], 1 % 3), (2, makeInputSet ["call"], 1 % 3), (3, makeInputSet ["ret"], 1 % 3)]) ]
  , epopaDeltaPop =
      [ (1, 1, [(1, makeInputSet ["call"], 1)])
      , (1, 2, [(1, makeInputSet ["call"], 1)])
      , (2, 1, [(2, makeInputSet ["call"], 1)])
      , (2, 2, [(2, makeInputSet ["call"], 1)])
      , (3, 1, [(3, makeInputSet ["ret"], 1)])
      , (3, 2, [(3, makeInputSet ["ret"], 1)])
      , (1, 0, [(0, makeInputSet ["call"], 1)])
      , (2, 0, [(0, makeInputSet ["call"], 1)])
      , (3, 0, [(0, makeInputSet ["call"], 1)])
      --, (2, 2, [(2, makeInputSet ["ret"], 1 :: Prob)])
      ]
  }

-- Paper example
loopFunShort :: ExplicitPopa Word String
loopFunShort = ExplicitPopa
  { epAlphabet = stlV3Alphabet
  , epInitial = (0, makeInputSet ["call"])
  , epopaDeltaPush =
      [ (0, [(1, makeInputSet ["call"], 1)])
      , (1, [(1, makeInputSet ["call"], 2 % 3), (2, makeInputSet ["ret"], 1 % 3)])
      , (3, [(3, makeInputSet ["call"], 1)])
      ]
  , epopaDeltaShift =
      [ (2, [(1, makeInputSet ["ret"], 1)]) ]
  , epopaDeltaPop =
      [ (1, 1, [(1, makeInputSet ["call"], 1 % 2), (2, makeInputSet ["ret"], 1 % 2)])
      , (1, 0, [(3, makeInputSet ["call"], 1)])
      ]
  }

loopFunStm :: ExplicitPopa Word String
loopFunStm = ExplicitPopa
  { epAlphabet = stlV3Alphabet
  , epInitial = (0, makeInputSet ["call"])
  , epopaDeltaPush =
      [ (0, [(1, makeInputSet ["stm"], 1)])
      , (1, [(0, makeInputSet ["call"], 2 % 3), (2, makeInputSet ["ret"], 1 % 3)])
      ]
  , epopaDeltaShift =
      [ (2, [(2, makeInputSet ["ret"], 1)]) ]
  , epopaDeltaPop =
      [ (2, 0, [(1, makeInputSet ["stm"], 1)])
      , (2, 1, [(2, makeInputSet ["ret"], 1)])
      , (0, 1, [(0, makeInputSet ["call"], 1)])
      ]
  }

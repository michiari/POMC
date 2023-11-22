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
import Pomc.Test.OPMs (stlV2Alphabet, stlV3Alphabet, makeInputSet)
import Data.Maybe(fromJust, isJust)
import Pomc.Potl (Formula(..), Dir(..))
import Pomc.Prob.ProbModelChecker (ExplicitPopa(..), qualitativeModelCheckExplicitGen)

import Data.Ratio((%))

tests :: TestTree
tests = testGroup "ProbModelChecking.hs Qualitative Tests" [symmetricRandomWalkTests]

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
                              (7, 8, [(9, makeInputSet ["ret", "perr"], 1 :: Prob)]),
                              (7, 0, [(10, makeInputSet ["ret"], 1 :: Prob)])
                            ]
                        }

expectedSymmetricRandomWalk :: [Bool]
expectedSymmetricRandomWalk = [ True
                              ]


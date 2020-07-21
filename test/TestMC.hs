module TestMC (tests) where

import Test.Tasty
import Test.Tasty.HUnit
import qualified TestSat (cases)
import Pomc.Prop (Prop(..))
import Pomc.Example (stlPrecRelV2, stlPrecV2sls)
import Pomc.PotlV2 (Formula)
import Pomc.ModelChecker (ExplicitOpa(..), modelCheckGen)

import Data.Set (Set)
import qualified Data.Set as Set

tests :: TestTree
tests = testGroup "TestMC.hs Tests" [baseTests]

baseTests :: TestTree
baseTests = testGroup "MC Base Tests" $ map makeTestCase (zip TestSat.cases expectedBase)

makeTestCase :: ((String, Formula String, [String], Bool), Bool) -> TestTree
makeTestCase ((name, phi, _, _), expected) =
  testCase (name ++ " (" ++ show phi ++ ")") $ modelCheckGen phi simpleExc @?= expected


makeInputSet :: (Ord a) => [a] -> Set (Prop a)
makeInputSet ilst = Set.fromList $ map Prop ilst

-- State encoding:
-- M0 = 0, A0 = 1, A1 = 2, B0 = 3, C0 = 4,
-- A2 = 5, A3 = 6, Er = 7, A4 = 8, Ar = 9, Ar' = 11, Mr = 10
-- Ar' is needed to enforce the final ret pa.
simpleExc :: ExplicitOpa Word String
simpleExc = ExplicitOpa
            { sigma = (stlPrecV2sls, map Prop ["pa", "pb", "pc", "perr"])
            , precRel = stlPrecRelV2
            , initials = [0]
            , finals = [10]
            , deltaPush =
                [ (0, makeInputSet ["call", "pa"],   [1])
                , (1, makeInputSet ["han"],          [2])
                , (2, makeInputSet ["call", "pb"],   [3])
                , (3, makeInputSet ["call", "pc"],   [4])
                , (4, makeInputSet ["call", "pc"],   [4])
                , (6, makeInputSet ["call", "perr"], [7])
                , (8, makeInputSet ["call", "perr"], [7])
                ]
            , deltaShift =
              [ (4, makeInputSet ["exc"],         [5])
              , (7, makeInputSet ["ret", "perr"], [7])
              , (9, makeInputSet ["ret", "pa"],   [11])
              ]
            , deltaPop =
              [ (4, 2, [4])
              , (4, 3, [4])
              , (4, 4, [4])
              , (5, 1, [6])
              , (7, 6, [8])
              , (7, 8, [9])
              , (11, 0, [10])
              ]
            }

expectedBase :: [Bool]
expectedBase = [True, False, False, False, False, False,
                False, False, False, True, True, False,
                True, False, True, False, False, False,
                False, False, False, False]

module TestMC (tests) where

import Test.Tasty
import Test.Tasty.HUnit
import qualified TestSat (cases)
import qualified EvalFormulas (formulas)
import Pomc.Prop (Prop(..))
import Pomc.Example (stlPrecRelV2, stlPrecV2sls)
import Pomc.PotlV2 (Formula)
import Pomc.ModelChecker (ExplicitOpa(..), modelCheckGen)

import Data.Set (Set)
import qualified Data.Set as Set

tests :: TestTree
tests = testGroup "ModelChecking.hs Tests" [sasBaseTests, sasEvalTests,
                                            lRBaseTests, lREvalTests]

sasBaseTests :: TestTree
sasBaseTests = testGroup "SAS OPA: MC Base Tests" $
  map (makeTestCase simpleExc) (zip TestSat.cases expectedSasBase)

sasEvalTests :: TestTree
sasEvalTests = testGroup "SAS OPA: MC Eval Tests" $
  map (makeTestCase simpleExc) (zip EvalFormulas.formulas expectedSasEval)


lRBaseTests :: TestTree
lRBaseTests = testGroup "LargerRec OPA: MC Base Tests" $
  map (makeTestCase largerRec) (zip TestSat.cases expectedLargerRecBase)

lREvalTests :: TestTree
lREvalTests = testGroup "LargerRec OPA: MC Eval Tests" $
  map (makeTestCase largerRec) (zip EvalFormulas.formulas expectedLargerRecEval)


makeTestCase :: ExplicitOpa Word String
             -> ((String, Formula String, [String], Bool), Bool)
             -> TestTree
makeTestCase opa ((name, phi, _, _), expected) =
  testCase (name ++ " (" ++ show phi ++ ")") $ modelCheckGen phi opa @?= expected


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

expectedSasBase :: [Bool]
expectedSasBase = [True, False, False, False, False, False,
                   False, False, False, True, True, False,
                   True, False, True, False, False, False,
                   False, False, False, False
                  ]

expectedSasEval :: [Bool]
expectedSasEval = [True, True, True, True,     -- chain_next
                   True, False,                -- contains_exc
                   True,                       -- data_access
                   False, False, True,         -- empty_frame
                   True,                       -- exception_safety
                   False, False, False, False, -- hier_down
                   False,                      -- hier_insp
                   True,                       -- hier_insp_exc
                   True, True, False, False,   -- hier_up
                   False, False,               -- normal_ret
                   True, True,                 -- no_throw
                   True, True,                 -- stack_inspection
                   False,                      -- uninstall_han
                   False, True, True,          -- until_exc
                   True, True, False           -- until_misc
                  ]

largerRec :: ExplicitOpa Word String
largerRec = ExplicitOpa
            { sigma = (stlPrecV2sls, map Prop ["pa", "pb", "pc", "perr", "eb"])
            , precRel = stlPrecRelV2
            , initials = [0]
            , finals = [8]
            , deltaPush =
                [ (0,  makeInputSet ["call", "pa"],    [1])
                , (1,  makeInputSet ["call", "pb"],    [2])
                , (2,  makeInputSet ["call", "pc"],    [3])
                , (2,  makeInputSet ["han"],           [4])
                , (3,  makeInputSet ["call", "pb"],    [2])
                , (4,  makeInputSet ["call", "pc"],    [3])
                , (7,  makeInputSet ["exc", "eb"],     [8])
                , (9,  makeInputSet ["call", "perr"], [10])
                , (10, makeInputSet ["call", "perr"], [10])
                , (15, makeInputSet ["han"],          [19])
                , (19, makeInputSet ["call", "pc"],    [3])
                , (23, makeInputSet ["call", "perr"], [10])
                ]
            , deltaShift =
                [ (9,  makeInputSet ["exc"],          [9])
                , (10, makeInputSet ["ret", "perr"], [11])
                , (12, makeInputSet ["ret", "perr"], [11])
                , (13, makeInputSet ["ret", "pb"],   [14])
                , (16, makeInputSet ["ret", "pc"],   [17])
                , (20, makeInputSet ["exc"],         [23])
                , (21, makeInputSet ["ret", "pa"],   [22])
                ]
            , deltaPop =
                [ (3,   2,  [5])
                , (3,   4,  [9])
                , (3,  19, [20])
                , (5,   1,  [6])
                , (5,   3, [18])
                , (6,   0,  [7])
                , (8,   7,  [8])
                , (9,   2,  [9])
                , (11, 10, [12])
                , (11,  9, [13])
                , (11, 23, [21])
                , (14,  1, [15])
                , (14,  3, [16])
                , (17,  4, [17])
                , (17,  2, [13])
                , (17, 19, [21])
                , (18,  2,  [5])
                , (18,  4,  [9])
                , (18, 19, [20])
                , (22,  0,  [8])
                , (23, 15, [23])
                ]
            }

expectedLargerRecBase :: [Bool]
expectedLargerRecBase = [True, False, False, False, False, False,
                         True, False, False, False, False, False,
                         False, False, False, False, False, False,
                         False, False, False, False
                        ]

expectedLargerRecEval :: [Bool]
expectedLargerRecEval = [False, False, False, False, -- chain_next
                         False, False,               -- contains_exc
                         True,                       -- data_access
                         False, False, False,        -- empty_frame
                         True,                       -- exception_safety
                         False, False, False, False, -- hier_down
                         False,                      -- hier_insp
                         False,                      -- hier_insp_exc
                         False, False, False, False, -- hier_up
                         False, False,               -- normal_ret
                         False, False,               -- no_throw
                         False, True,                -- stack_inspection
                         False,                      -- uninstall_han
                         False, True, False,         -- until_exc
                         False, False, False         -- until_misc
                        ]

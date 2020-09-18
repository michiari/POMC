module TestMC (tests) where

import Test.Tasty
import Test.Tasty.HUnit
import qualified TestSat (cases)
import EvalFormulas (ap, formulas)
import Pomc.Prop (Prop(..))
import Pomc.Example (stlPrecRelV2, stlPrecV2sls)
import Pomc.PotlV2 (Formula(..), Dir(..))
import Pomc.ModelChecker (ExplicitOpa(..), modelCheckGen)

import Data.Set (Set)
import qualified Data.Set as Set

tests :: TestTree
tests = testGroup "ModelChecking.hs Tests" [sasBaseTests, sasEvalTests,
                                            lRBaseTests, lREvalTests,
                                            inspectionTest, overflowTest,
                                            jensenTests, jensenFullTests]

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


inspectionTest :: TestTree
inspectionTest = testGroup "Stack Inspection OPA" $
  [makeTestCase inspection (("If perr is called, pa is not on the stack."
                            , Always $ (ap "call" `And` ap "perr") `Implies`
                              (Not $ Since Down T (ap "pa"))
                            , []
                            , True)
                           , True)]

overflowTest :: TestTree
overflowTest = testGroup "Stack Overflow" $
  [makeTestCase inspection (("The stack is never deeper than 3."
                            , Always . Not $ maxStackDepth 3
                            , []
                            , True)
                           , False)]

maxStackDepth :: Int -> Formula String
maxStackDepth 0 = ap "call"
maxStackDepth n = ap "call" `And` ((XBack Down $ maxStackDepth (n-1))
                                    `Or` (PBack Down $ maxStackDepth (n-1)))

inspection :: ExplicitOpa Word String
inspection = ExplicitOpa
  { sigma = (stlPrecV2sls, map Prop ["pa", "pb", "pc", "pd", "pe", "perr"])
            , precRel = stlPrecRelV2
            , initials = [0]
            , finals = [5]
            , deltaPush =
                [ (0, makeInputSet ["call", "pa"],    [6])
                , (1, makeInputSet ["han"], [2])
                , (2, makeInputSet ["call", "pa"], [6])
                , (3, makeInputSet ["call", "pb"], [11])
                , (4, makeInputSet ["call", "perr"], [28])
                , (6, makeInputSet ["call", "pc"], [16, 17])
                , (7, makeInputSet ["call", "pd"], [20])
                , (8, makeInputSet ["call", "pa"], [6])
                , (11, makeInputSet ["han"], [12])
                , (12, makeInputSet ["call", "pe"], [24, 26])
                , (13, makeInputSet ["call", "perr"], [28])
                , (16, makeInputSet ["call", "pa"], [6])
                , (17, makeInputSet ["call", "pe"], [24, 26])
                , (20, makeInputSet ["call", "pc"], [16, 17])
                , (21, makeInputSet ["call", "pa"], [6])
                , (24, makeInputSet ["exc"], [5])
                ]
            , deltaShift =
                [ (9, makeInputSet ["ret", "pa"], [10])
                , (14, makeInputSet ["ret", "pb"], [15])
                , (18, makeInputSet ["ret", "pc"], [19])
                , (22, makeInputSet ["ret", "pd"], [23])
                , (24, makeInputSet ["exc"], [25])
                , (26, makeInputSet ["ret", "pe"], [27])
                , (28, makeInputSet ["ret", "perr"], [29])
                ]
            , deltaPop =
                [ (5, 24, [5])
                , (10, 0, [1])
                , (10, 2, [3])
                , (15, 3, [5])
                , (19, 6, [7])
                , (19, 20, [21])
                , (23, 7, [8, 9])
                , (24, 12, [24])
                , (24, 3, [24])
                , (24, 17, [24])
                , (24, 6, [24])
                , (24, 0, [24])
                , (24, 2, [24])
                , (24, 8, [24])
                , (24, 16, [24])
                , (24, 21, [24])
                , (25, 11, [13])
                , (25, 1, [4])
                , (27, 17, [18])
                , (27, 12, [14])
                , (29, 4, [5])
                , (29, 13, [14])
                ]
            }


jensenTests :: TestTree
jensenTests = testGroup "Jensen Tests" [jensenRd, jensenWr]

jensenRd :: TestTree
jensenRd = makeTestCase jensen (("Only privileged reads."
                                , Always $ ((ap "call" `And` ap "raw_rd")
                                            `Implies`
                                             (Not $ Since Down T
                                               (ap "call"
                                                `And` (Not $ ap "P_all")
                                                `And` (Not $ ap "raw_rd"))))
                                , []
                                , True)
                               , True)

jensenWr :: TestTree
jensenWr = makeTestCase jensen (("Only privileged writes."
                                , Always $ ((ap "call" `And` ap "raw_wr")
                                            `Implies`
                                             (Not $ Since Down T
                                               (ap "call"
                                                `And` (Not $ ap "P_all")
                                                `And` (Not $ ap "raw_wr"))))
                                , []
                                , True)
                               , True)

jensen :: ExplicitOpa Word String
jensen = ExplicitOpa
  { sigma = (stlPrecV2sls, map Prop ["sp", "cl", "cp", "db", "rd", "wr", "raw_rd", "raw_wr", "P_all"])
  , precRel = stlPrecRelV2
  , initials = [0]
  , finals = [2]
  , deltaPush =
      [ (0, makeInputSet ["call", "sp", "P_all"], [3])
      , (1, makeInputSet ["call", "cl"], [8])
      , (3, makeInputSet ["call", "cp", "P_all"], [12])
      , (4, makeInputSet ["call", "db", "P_all"], [18])
      , (5, makeInputSet ["call", "sp", "P_all"], [3])
      , (8, makeInputSet ["call", "db"], [25])
      , (9, makeInputSet ["call", "cl"], [8])
      , (12, makeInputSet ["call", "rd", "P_all"], [27])
      , (16, makeInputSet ["exc"], [2])
      , (18, makeInputSet ["call", "cp", "P_all"], [12])
      , (19, makeInputSet ["call", "rd", "P_all"], [27])
      , (20, makeInputSet ["call", "wr", "P_all"], [32])
      , (21, makeInputSet ["exc"], [2])
      , (25, makeInputSet ["exc"], [2])
      , (27, makeInputSet ["call", "raw_rd"], [37])
      , (30, makeInputSet ["exc"], [2])
      , (32, makeInputSet ["call", "raw_wr"], [39])
      , (35, makeInputSet ["exc"], [2])
      ]
  , deltaShift =
      [ (6, makeInputSet ["ret", "sp", "P_all"], [7])
      , (10, makeInputSet ["ret", "cl"], [11])
      , (13, makeInputSet ["ret", "cp", "P_all"], [41])
      , (14, makeInputSet ["ret", "cp", "P_all"], [15])
      , (16, makeInputSet ["exc"], [17])
      , (21, makeInputSet ["exc"], [22])
      , (23, makeInputSet ["ret", "db", "P_all"], [24])
      , (25, makeInputSet ["exc"], [26])
      , (28, makeInputSet ["ret", "rd", "P_all"], [29])
      , (30, makeInputSet ["exc"], [31])
      , (33, makeInputSet ["ret", "wr", "P_all"], [34])
      , (35, makeInputSet ["exc"], [36])
      , (37, makeInputSet ["ret", "raw_rd"], [38])
      , (39, makeInputSet ["ret", "raw_wr"], [40])
      ]
  , deltaPop =
      [ (2, 16, [2])
      , (2, 21, [2])
      , (2, 25, [2])
      , (2, 30, [2])
      , (2, 35, [2])
      , (7, 0, [1])
      , (7, 5, [6])
      , (11, 1, [2])
      , (11, 9, [10])
      , (15, 3, [4])
      , (15, 18, [19])
      , (21, 0, [21])
      , (21, 4, [21])
      , (24, 4, [5, 6])
      , (25, 1, [25])
      , (25, 8, [25])
      , (29, 12, [13, 14])
      , (29, 19, [20])
      , (30, 1, [30])
      , (30, 8, [30])
      , (30, 25, [30])
      , (34, 20, [23])
      , (35, 1, [35])
      , (35, 8, [35])
      , (35, 25, [35])
      , (38, 27, [28])
      , (40, 32, [33])
      , (41, 3, [5, 6])
      , (41, 18, [21])
      ]
  }


jensenFullTests :: TestTree
jensenFullTests = testGroup "Jensen Full Privileges Tests" [ jensenFullRd, jensenFullWr
                                                           , jensenFullRdCp, jensenFullWrDb]

jensenFullRd :: TestTree
jensenFullRd = makeTestCase jensenFull
  (("Only privileged reads."
   , Always $ ((ap "call" `And` ap "raw_rd")
                `Implies`
                (Not $ Since Down T
                  (ap "call"
                    `And` (Not $ ap "P_rd")
                    `And` (Not $ ap "raw_rd"))))
   , []
   , True)
  , True)

jensenFullWr :: TestTree
jensenFullWr = makeTestCase jensenFull
  (("Only privileged writes."
   , Always $ ((ap "call" `And` ap "raw_wr")
                `Implies`
                (Not $ Since Down T
                  (ap "call"
                    `And` (Not $ ap "P_wr")
                    `And` (Not $ ap "raw_wr"))))
   , []
   , True)
  , True)

jensenFullRdCp :: TestTree
jensenFullRdCp = makeTestCase jensenFull
  (("Only reads with canpay privilege."
   , Always $ ((ap "call" `And` ap "raw_rd")
                `Implies`
                (Not $ Since Down T
                  (ap "call"
                    `And` (Not $ ap "P_cp")
                    `And` (Not $ ap "raw_rd"))))
   , []
   , True)
  , True)

jensenFullWrDb :: TestTree
jensenFullWrDb = makeTestCase jensenFull
  (("Only writes with debit privilege."
   , Always $ ((ap "call" `And` ap "raw_wr")
                `Implies`
                (Not $ Since Down T
                  (ap "call"
                    `And` (Not $ ap "P_db")
                    `And` (Not $ ap "raw_wr"))))
   , []
   , True)
  , True)

jensenFull :: ExplicitOpa Word String
jensenFull = ExplicitOpa
  { sigma = (stlPrecV2sls, map Prop ["sp", "cl", "cp", "db", "rd", "wr", "raw_rd", "raw_wr",
                                     "P_cp", "P_db", "P_rd", "P_wr"])
  , precRel = stlPrecRelV2
  , initials = [0]
  , finals = [2]
  , deltaPush =
      [ (0, makeInputSet ["call", "sp", "P_cp", "P_db", "P_rd", "P_wr"], [3])
      , (1, makeInputSet ["call", "cl"], [8])
      , (3, makeInputSet ["call", "cp", "P_cp", "P_db", "P_rd", "P_wr"], [12])
      , (4, makeInputSet ["call", "db", "P_cp", "P_db", "P_rd", "P_wr"], [18])
      , (5, makeInputSet ["call", "sp", "P_cp", "P_db", "P_rd", "P_wr"], [3])
      , (8, makeInputSet ["call", "db"], [25])
      , (9, makeInputSet ["call", "cl"], [8])
      , (12, makeInputSet ["call", "rd", "P_cp", "P_db", "P_rd", "P_wr"], [27])
      , (16, makeInputSet ["exc"], [2])
      , (18, makeInputSet ["call", "cp", "P_cp", "P_db", "P_rd", "P_wr"], [12])
      , (19, makeInputSet ["call", "rd", "P_cp", "P_db", "P_rd", "P_wr"], [27])
      , (20, makeInputSet ["call", "wr", "P_cp", "P_db", "P_rd", "P_wr"], [32])
      , (21, makeInputSet ["exc"], [2])
      , (25, makeInputSet ["exc"], [2])
      , (27, makeInputSet ["call", "raw_rd"], [37])
      , (30, makeInputSet ["exc"], [2])
      , (32, makeInputSet ["call", "raw_wr"], [39])
      , (35, makeInputSet ["exc"], [2])
      ]
  , deltaShift =
      [ (6, makeInputSet ["ret", "sp", "P_cp", "P_db", "P_rd", "P_wr"], [7])
      , (10, makeInputSet ["ret", "cl"], [11])
      , (13, makeInputSet ["ret", "cp", "P_cp", "P_db", "P_rd", "P_wr"], [41])
      , (14, makeInputSet ["ret", "cp", "P_cp", "P_db", "P_rd", "P_wr"], [15])
      , (16, makeInputSet ["exc"], [17])
      , (21, makeInputSet ["exc"], [22])
      , (23, makeInputSet ["ret", "db", "P_cp", "P_db", "P_rd", "P_wr"], [24])
      , (25, makeInputSet ["exc"], [26])
      , (28, makeInputSet ["ret", "rd", "P_cp", "P_db", "P_rd", "P_wr"], [29])
      , (30, makeInputSet ["exc"], [31])
      , (33, makeInputSet ["ret", "wr", "P_cp", "P_db", "P_rd", "P_wr"], [34])
      , (35, makeInputSet ["exc"], [36])
      , (37, makeInputSet ["ret", "raw_rd"], [38])
      , (39, makeInputSet ["ret", "raw_wr"], [40])
      ]
  , deltaPop =
      [ (2, 16, [2])
      , (2, 21, [2])
      , (2, 25, [2])
      , (2, 30, [2])
      , (2, 35, [2])
      , (7, 0, [1])
      , (7, 5, [6])
      , (11, 1, [2])
      , (11, 9, [10])
      , (15, 3, [4])
      , (15, 18, [19])
      , (21, 0, [21])
      , (21, 4, [21])
      , (24, 4, [5, 6])
      , (25, 1, [25])
      , (25, 8, [25])
      , (29, 12, [13, 14])
      , (29, 19, [20])
      , (30, 1, [30])
      , (30, 8, [30])
      , (30, 25, [30])
      , (34, 20, [23])
      , (35, 1, [35])
      , (35, 8, [35])
      , (35, 25, [35])
      , (38, 27, [28])
      , (40, 32, [33])
      , (41, 3, [5, 6])
      , (41, 18, [21])
      ]
  }



{- |
   Module      : Pomc.Test.TestMC
   Copyright   : 2021-2025 Michele Chiari
   License     : MIT
   Maintainer  : Michele Chiari
-}

module Pomc.Test.TestMC (tests, slowTests) where

import Test.Tasty
import Test.Tasty.HUnit
import Pomc.Test.OPMs (stlV2Alphabet, makeInputSet)
import Pomc.Test.EvalFormulas (TestCase, ap, zipExpected, excludeIndices, formulas)
import Pomc.Potl (Formula(..), Dir(..))
import Pomc.ModelChecker (ExplicitOpa(..), modelCheckExplicitGen)
import qualified Data.Set as Set (toList)

tests :: TestTree
tests = testGroup "ModelChecking.hs Tests" [ sasEvalTests, synthEvalTests, lREvalTests
                                           , inspectionTest, overflowTest
                                           , jensenTests, jensenFullTests
                                           , stackExcTests, stackExcSwapTests
                                           ]

sasEvalTests :: TestTree
sasEvalTests = testGroup "SAS OPA MC Eval Tests" $
  map (makeTestCase simpleExc) $ zipExpected formulas expectedSasEval

synthEvalTests :: TestTree
synthEvalTests = testGroup "SYNTH OPA MC Eval Tests" $
  map (makeTestCase synth) $ zipExpected formulas expectedSasEval

lREvalTests :: TestTree
lREvalTests = testGroup "LargerRec OPA MC Eval Tests" $
  map (makeTestCase largerRec) $ zipExpected lRFormulas expectedLargerRecEval
  where lRFormulas = excludeIndices formulas [18, 44]

-- finite model checking case
makeTestCase :: ExplicitOpa Word String
             -> (TestCase, Bool)
             -> TestTree
makeTestCase opa ((name, phi), expected) =
  let (sat, trace) = modelCheckExplicitGen False phi opa
      debugMsg False tr = "Expected True, got False. Counterexample:\n"
        ++ show (map (\(q, b) -> (q, Set.toList b)) tr)
      debugMsg True _ = "Expected False, got True."
  in testCase (name ++ " (" ++ show phi ++ ")") $ assertBool (debugMsg sat trace) (sat == expected)


-- State encoding:
-- M0 = 0, A0 = 1, A1 = 2, B0 = 3, C0 = 4,
-- A2 = 5, A3 = 6, Er = 7, A4 = 8, Ar = 9, Ar' = 11, Mr = 10
-- Ar' is needed to enforce the final ret pa.
simpleExc :: ExplicitOpa Word String
simpleExc = ExplicitOpa
            { eoAlphabet = stlV2Alphabet
            , eoInitials = [0]
            , eoFinals = [10]
            , eoDeltaPush =
                [ (0, makeInputSet ["call", "pa"],   [1])
                , (1, makeInputSet ["han"],          [2])
                , (2, makeInputSet ["call", "pb"],   [3])
                , (3, makeInputSet ["call", "pc"],   [4])
                , (4, makeInputSet ["call", "pc"],   [4])
                , (6, makeInputSet ["call", "perr"], [7])
                , (8, makeInputSet ["call", "perr"], [7])
                ]
            , eoDeltaShift =
                [ (4, makeInputSet ["exc"],         [5])
                , (7, makeInputSet ["ret", "perr"], [7])
                , (9, makeInputSet ["ret", "pa"],   [11])
                ]
            , eoDeltaPop =
                [ (4, 2, [4])
                , (4, 3, [4])
                , (4, 4, [4])
                , (5, 1, [6])
                , (7, 6, [8])
                , (7, 8, [9])
                , (11, 0, [10])
                ]
            }

expectedSasEval :: [Bool]
expectedSasEval =
  [ True, False, True, False, False, False
  , False, False, False, False, True, True
  , False, True, False, True, False, False
  , False, False, False, False, False, True -- base_tests
  , True, True, True, False, True    -- chain_next
  , True, False, False, True         -- contains_exc
  , True                             -- data_access
  , False, False, True, False        -- empty_frame
  , True                             -- exception_safety
  , False, False, False, False       -- hier_down
  , False                            -- hier_insp
  , True                             -- hier_insp_exc
  , True, True, False, False         -- hier_up
  , False, False                     -- normal_ret
  , True, True                       -- no_throw
  , True, True                       -- stack_inspection
  , False                            -- uninstall_han
  , False, True, True, True          -- until_exc
  , True, True, True                 -- until_misc
  ]


synth :: ExplicitOpa Word String
synth = ExplicitOpa
  { eoAlphabet = stlV2Alphabet
  , eoInitials = [0]
  , eoFinals = [1]
  , eoDeltaPush =
      [ (0, makeInputSet ["call", "pa"],[6])
      , (4, makeInputSet ["exc"],[1])
      , (6, makeInputSet ["han"],[7])
      , (7, makeInputSet ["call", "pb"],[12])
      , (10, makeInputSet ["exc"],[1])
      , (12, makeInputSet ["call", "pc"],[15,17])
      , (15, makeInputSet ["exc"],[1])
      , (17, makeInputSet ["call", "pc"],[15,17])
      , (21, makeInputSet ["call", "perr"],[22])
      , (24, makeInputSet ["exc"],[1])
      , (27, makeInputSet ["call", "perr"],[22])
      ]
  , eoDeltaShift =
      [ (2, makeInputSet ["pa", "ret"],[3])
      , (4, makeInputSet ["exc"],[5])
      , (8, makeInputSet ["pb", "ret"],[9])
      , (10, makeInputSet ["exc"],[11])
      , (13, makeInputSet ["pc", "ret"],[14])
      , (15, makeInputSet ["exc"],[16])
      , (22, makeInputSet ["perr", "ret"],[23])
      , (24, makeInputSet ["exc"],[25])
      ]
  , eoDeltaPop =
    [ (1,4,[1])
    , (1,10,[1])
    , (1,15,[1])
    , (1,24,[1])
    , (3,0,[1])
    , (5,6,[21])
    , (9,7,[2])
    , (10,7,[4])
    , (14,12,[8])
    , (14,17,[13])
    , (15,12,[10])
    , (15,17,[15])
    , (23,21,[27])
    , (23,27,[2])
    , (24,21,[4])
    , (24,27,[4])
    ]
  }


largerRec :: ExplicitOpa Word String
largerRec = ExplicitOpa
            { eoAlphabet = stlV2Alphabet
            , eoInitials = [0]
            , eoFinals = [8]
            , eoDeltaPush =
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
            , eoDeltaShift =
                [ (9,  makeInputSet ["exc"],          [9])
                , (10, makeInputSet ["ret", "perr"], [11])
                , (12, makeInputSet ["ret", "perr"], [11])
                , (13, makeInputSet ["ret", "pb"],   [14])
                , (16, makeInputSet ["ret", "pc"],   [17])
                , (20, makeInputSet ["exc"],         [23])
                , (21, makeInputSet ["ret", "pa"],   [22])
                ]
            , eoDeltaPop =
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

expectedLargerRecEval :: [Bool]
expectedLargerRecEval =
  [ True, False, True, False, False, False
  , False, True, False, False, False, False
  , False, False, False, False, False, False
  , False, False, False, False, False -- base_tests
  , False, False, False, False, False -- chain_next
  , False, False, False, False        -- contains_exc
  , True                              -- data_access
  , False, False, False, False        -- empty_frame
  , True                              -- exception_safety
  , False, False, False, False        -- hier_down
  , False                             -- hier_insp
  , False, False, False, False        -- hier_up
  , False, False                      -- normal_ret
  , False, False                      -- no_throw
  , False, True                       -- stack_inspection
  , False                             -- uninstall_han
  , False, True, True, False          -- until_exc
  , False, False, False               -- until_misc
  ]


inspectionTest :: TestTree
inspectionTest = testGroup "Stack Inspection OPA" $
  [makeTestCase inspection (("If perr is called, pa is not on the stack."
                            , Always $ (ap "call" `And` ap "perr") `Implies`
                              (Not $ Since Down T (ap "pa")))
                           , True)]

overflowTest :: TestTree
overflowTest = testGroup "Stack Overflow" $
  [makeTestCase inspection (("The stack is never deeper than 3."
                            , Always . Not $ maxStackDepth 3)
                           , False)]

maxStackDepth :: Int -> Formula String
maxStackDepth 0 = ap "call"
maxStackDepth n = ap "call" `And` ((XBack Down $ maxStackDepth (n-1))
                                    `Or` (PBack Down $ maxStackDepth (n-1)))

inspection :: ExplicitOpa Word String
inspection = ExplicitOpa
  { eoAlphabet = stlV2Alphabet
  , eoInitials = [0]
  , eoFinals = [5]
  , eoDeltaPush =
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
  , eoDeltaShift =
      [ (9, makeInputSet ["ret", "pa"], [10])
      , (14, makeInputSet ["ret", "pb"], [15])
      , (18, makeInputSet ["ret", "pc"], [19])
      , (22, makeInputSet ["ret", "pd"], [23])
      , (24, makeInputSet ["exc"], [25])
      , (26, makeInputSet ["ret", "pe"], [27])
      , (28, makeInputSet ["ret", "perr"], [29])
      ]
  , eoDeltaPop =
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
                                                `And` (Not $ ap "raw_rd")))))
                               , True)

jensenWr :: TestTree
jensenWr = makeTestCase jensen (("Only privileged writes."
                                , Always $ ((ap "call" `And` ap "raw_wr")
                                            `Implies`
                                             (Not $ Since Down T
                                               (ap "call"
                                                `And` (Not $ ap "P_all")
                                                `And` (Not $ ap "raw_wr")))))
                               , True)

jensen :: ExplicitOpa Word String
jensen = ExplicitOpa
  { eoAlphabet = stlV2Alphabet
  , eoInitials = [0]
  , eoFinals = [2]
  , eoDeltaPush =
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
  , eoDeltaShift =
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
  , eoDeltaPop =
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
                                                           , jensenFullRdCp, jensenFullWrDb
                                                           ]

jensenFullRd :: TestTree
jensenFullRd = makeTestCase jensenFull
  (("Only privileged reads."
   , Always $ ((ap "call" `And` ap "raw_rd")
                `Implies`
                (Not $ Since Down T
                  (ap "call"
                    `And` (Not $ ap "P_rd")
                    `And` (Not $ ap "raw_rd")))))
  , True)

jensenFullWr :: TestTree
jensenFullWr = makeTestCase jensenFull
  (("Only privileged writes."
   , Always $ ((ap "call" `And` ap "raw_wr")
                `Implies`
                (Not $ Since Down T
                  (ap "call"
                    `And` (Not $ ap "P_wr")
                    `And` (Not $ ap "raw_wr")))))
  , True)

jensenFullRdCp :: TestTree
jensenFullRdCp = makeTestCase jensenFull
  (("Only reads with canpay privilege."
   , Always $ ((ap "call" `And` ap "raw_rd")
                `Implies`
                (Not $ Since Down T
                  (ap "call"
                    `And` (Not $ ap "P_cp")
                    `And` (Not $ ap "raw_rd")))))
  , True)

jensenFullWrDb :: TestTree
jensenFullWrDb = makeTestCase jensenFull
  (("Only writes with debit privilege."
   , Always $ ((ap "call" `And` ap "raw_wr")
                `Implies`
                (Not $ Since Down T
                  (ap "call"
                    `And` (Not $ ap "P_db")
                    `And` (Not $ ap "raw_wr")))))
  , True)

jensenFull :: ExplicitOpa Word String
jensenFull = ExplicitOpa
  { eoAlphabet = stlV2Alphabet
  , eoInitials = [0]
  , eoFinals = [2]
  , eoDeltaPush =
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
  , eoDeltaShift =
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
  , eoDeltaPop =
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



stackExcTests :: TestTree
stackExcTests = testGroup "Exception Safety Unsafe Stack" [ stackExcConsistent
                                                          , stackExcNeutral
                                                          , stackExcNeutralS
                                                          ]

stackExcConsistent :: TestTree
stackExcConsistent = makeTestCase stackExc
  (("The stack is left in a consistent state."
   , Always $ (ap "exc"
               `Implies`
               (Not $ (PBack Up (ap "tainted")
                       `Or` XBack Up (ap "tainted"))
                `And` XBack Up (ap "Stack::push(const T&)" `Or` ap "Stack::pop()"))))
  , False)

stackExcNeutral :: TestTree
stackExcNeutral = makeTestCase stackExc
  (("All Stack member functions are exception neutral."
   , Always ((ap "exc"
              `And` PBack Up (ap "T")
              `And` XBack Down (ap "han"))
              `Implies`
              (XBack Down $ XBack Down $ XNext Up $ ap "exc")))
  , True)

stackExcNeutralS :: TestTree
stackExcNeutralS = makeTestCase stackExc
  (("All Stack member functions are exception neutral (slow)."
   , Always ((ap "exc"
              `And` PBack Up (ap "T")
              `And` XBack Down (ap "han" `And` XBack Down (ap "Stack")))
              `Implies`
              (XBack Down $ XBack Down $ XNext Up $ ap "exc")))
  , True)

stackExc :: ExplicitOpa Word String
stackExc = ExplicitOpa
  { eoAlphabet = stlV2Alphabet
  , eoInitials = [0]
  , eoFinals = [6]
  , eoDeltaPush =
      [ (0, makeInputSet ["call", "Stack", "Stack::Stack()"], [7])
      , (1, makeInputSet ["call", "Stack", "Stack::push(const T&)"], [36, 38])
      , (2, makeInputSet ["call", "Stack", "Stack::push(const T&)"], [36, 38])
      , (3, makeInputSet ["call", "Stack", "Stack::size() const"], [34])
      , (4, makeInputSet ["call", "Stack", "Stack::pop()"], [41, 43])
      , (5, makeInputSet ["call", "Stack", "Stack::~Stack()"], [17])
      , (7, makeInputSet ["call", "T", "T::operator new()"], [62, 22])
      , (10, makeInputSet ["call", "Stack", "Stack::NewCopy(...)"], [26])
      , (13, makeInputSet ["call", "Stack", "Stack::NewCopy(...)"], [26])
      , (14, makeInputSet ["call", "T", "T::operator delete()"], [24])
      , (17, makeInputSet ["call", "T", "T::operator delete()"], [24])
      , (62, makeInputSet ["call", "T", "T::T()"], [58, 60])
      , (22, makeInputSet ["exc"], [6])
      , (26, makeInputSet ["call", "T", "T::operator new()"], [62, 22])
      , (27, makeInputSet ["han"], [28])
      , (28, makeInputSet ["call", "std::copy(...)"], [47])
      , (31, makeInputSet ["call", "T", "T::operator delete()"], [24])
      , (32, makeInputSet ["exc"], [6])
      , (36, makeInputSet ["call", "Stack", "Stack::NewCopy(...)"], [26])
      , (37, makeInputSet ["call", "T", "T::operator delete()"], [24])
      , (38, makeInputSet ["call", "T", "T::operator=(const T&)", "tainted"], [54, 56])
      , (41, makeInputSet ["exc"], [5])
      , (43, makeInputSet ["call", "T", "T::T(const T&)"], [50, 52])
      , (44, makeInputSet ["call", "T", "T::T(const T&)", "tainted"], [50, 52])
      , (47, makeInputSet ["call", "T", "T::operator=(const T&)"], [54, 56])
      , (52, makeInputSet ["exc"], [6])
      , (56, makeInputSet ["exc"], [6])
      , (60, makeInputSet ["exc"], [6])
      ]
  , eoDeltaShift =
      [ (8, makeInputSet ["ret", "Stack", "Stack::Stack()"], [9])
      , (11, makeInputSet ["ret", "Stack", "Stack::Stack(const Stack<T>&)"], [12])
      , (15, makeInputSet ["ret", "Stack", "Stack::operator=(const Stack<T>&)"], [16])
      , (18, makeInputSet ["ret", "Stack", "Stack::~Stack()"], [19])
      , (20, makeInputSet ["ret", "T", "T::operator new()"], [21])
      , (22, makeInputSet ["exc"], [23])
      , (24, makeInputSet ["ret", "T", "T::operator delete()"], [25])
      , (29, makeInputSet ["ret", "Stack", "Stack::NewCopy(...)"], [30])
      , (32, makeInputSet ["exc"], [33])
      , (34, makeInputSet ["ret", "Stack", "Stack::size() const"], [35])
      , (39, makeInputSet ["ret", "Stack", "Stack::push(const T&)", "tainted"], [40])
      , (41, makeInputSet ["exc"], [42])
      , (45, makeInputSet ["ret", "Stack", "Stack::pop()", "tainted"], [46])
      , (48, makeInputSet ["ret", "std::copy(...)"], [49])
      , (50, makeInputSet ["ret", "T", "T::T(const T&)"], [51])
      , (52, makeInputSet ["exc"], [53])
      , (54, makeInputSet ["ret", "T", "T::operator=(const T&)"], [55])
      , (56, makeInputSet ["exc"], [57])
      , (58, makeInputSet ["ret", "T", "T::T()"], [59])
      , (60, makeInputSet ["exc"], [61])
      ]
  , eoDeltaPop =
      [ (6, 22, [6])
      , (6, 32, [6])
      , (6, 41, [6])
      , (6, 52, [6])
      , (6, 56, [6])
      , (6, 60, [6])
      , (9, 0, [1])
      , (19, 5, [6])
      , (21, 7, [8])
      , (21, 26, [27])
      , (22, 0, [22])
      , (22, 1, [22])
      , (22, 2, [22])
      , (22, 7, [22])
      , (22, 10, [22])
      , (22, 13, [22])
      , (22, 26, [22])
      , (22, 36, [22])
      , (25, 14, [15])
      , (25, 17, [18])
      , (25, 31, [32])
      , (25, 37, [38])
      , (30, 10, [10])
      , (30, 13, [14])
      , (30, 36, [37])
      , (32, 1, [32])
      , (32, 2, [32])
      , (32, 10, [32])
      , (32, 13, [32])
      , (32, 36, [32])
      , (35, 3, [4])
      , (40, 1, [2])
      , (40, 2, [3])
      , (41, 4, [41])
      , (46, 4, [6])
      , (49, 28, [29])
      , (51, 43, [44])
      , (51, 44, [45])
      , (52, 4, [52])
      , (52, 43, [52])
      , (52, 44, [52])
      , (55, 38, [39])
      , (55, 43, [44])
      , (55, 47, [48])
      , (56, 1, [56])
      , (56, 2, [56])
      , (56, 10, [56])
      , (56, 13, [56])
      , (56, 28, [56])
      , (56, 36, [56])
      , (56, 38, [56])
      , (56, 47, [56])
      , (57, 27, [31])
      , (59, 62, [20])
      , (60, 0, [60])
      , (60, 1, [60])
      , (60, 2, [60])
      , (60, 7, [60])
      , (60, 10, [60])
      , (60, 13, [60])
      , (60, 26, [60])
      , (60, 36, [60])
      , (60, 62, [60])
      ]
  }


stackExcSwapTests :: TestTree
stackExcSwapTests = testGroup "Exception Safety Safe Stack" [ stackExcSwapConsistent
                                                            , stackExcSwapNeutral
                                                            , stackExcSwapNeutralS
                                                            ]

stackExcSwapConsistent :: TestTree
stackExcSwapConsistent = makeTestCase stackExcSwap
  (("The stack is left in a consistent state."
   , Always $ (ap "exc"
               `Implies`
               (Not $ (PBack Up (ap "tainted")
                       `Or` XBack Up (ap "tainted"))
                `And` XBack Up (ap "Stack::Push(const T&)" `Or` ap "Stack::Pop()"))))
  , True)

stackExcSwapNeutral :: TestTree
stackExcSwapNeutral = makeTestCase stackExcSwap
  (("All Stack member functions are exception neutral."
   , Always ((ap "exc"
              `And` PBack Up (ap "T")
              `And` XBack Down (ap "han"))
              `Implies`
              (XBack Down $ XBack Down $ XNext Up $ ap "exc")))
  , True)

stackExcSwapNeutralS :: TestTree
stackExcSwapNeutralS = makeTestCase stackExcSwap
  (("All Stack member functions are exception neutral (slow)."
   , Always ((ap "exc"
              `And` PBack Up (ap "T")
              `And` XBack Down (ap "han" `And` XBack Down (ap "Stack")))
              `Implies`
              (XBack Down $ XBack Down $ XNext Up $ ap "exc")))
  , True)


stackExcSwap :: ExplicitOpa Word String
stackExcSwap = ExplicitOpa
  { eoAlphabet = stlV2Alphabet
  , eoInitials = [0]
  , eoFinals = [6]
  , eoDeltaPush =
      [ (0, makeInputSet ["call", "Stack", "Stack::Stack()"], [7])
      , (1, makeInputSet ["call", "Stack", "Stack::Push(const T&)"], [40, 45])
      , (2, makeInputSet ["call", "Stack", "Stack::Push(const T&)"], [40, 45])
      , (3, makeInputSet ["call", "Stack", "Stack::Size() const"], [28])
      , (4, makeInputSet ["call", "Stack", "Stack::Pop()"], [56, 58])
      , (5, makeInputSet ["call", "Stack", "Stack::~Stack()"], [37])
      , (7, makeInputSet ["call", "::operator new()"], [10, 12])
      , (12, makeInputSet ["exc"], [6])
      , (16, makeInputSet ["call", "std::destroy<T>()"], [61])
      , (17, makeInputSet ["call", "::operator delete()"], [14])
      , (20, makeInputSet ["call", "Stack", "StackImpl::StackImpl(size_t)"], [7])
      , (23, makeInputSet ["call", "std::swap()"], [72])
      , (24, makeInputSet ["call", "std::swap()", "tainted"], [72])
      , (25, makeInputSet ["call", "std::swap()", "tainted"], [72])
      , (30, makeInputSet ["call", "Stack", "StackImpl::StackImpl(size_t)"], [7])
      , (31, makeInputSet ["call", "T", "T::T(const T&)"], [68, 70])
      , (34, makeInputSet ["call", "Stack", "Stack::Stack(const Stack<T>&)"], [20])
      , (35, makeInputSet ["call", "Stack", "StackImpl::Swap(StackImpl<T>&)"], [23])
      , (37, makeInputSet ["call", "Stack", "StackImpl::~StackImpl()"], [16])
      , (40, makeInputSet ["call", "Stack", "Stack::Stack(const Stack<T>&)"], [20])
      , (41, makeInputSet ["han"], [42])
      , (42, makeInputSet ["call", "T", "T::T(const T&)"], [68, 70])
      , (43, makeInputSet ["call", "T", "T::T(const T&)"], [68, 70])
      , (44, makeInputSet ["call", "Stack", "StackImpl::Swap(StackImpl<T>&)"], [23])
      , (45, makeInputSet ["call", "T", "T::T(const T&)"], [68, 70])
      , (48, makeInputSet ["call", "Stack", "Stack::~Stack()"], [37])
      , (49, makeInputSet ["exc"], [6])
      , (51, makeInputSet ["exc"], [6])
      , (53, makeInputSet ["call", "T", "T::T(const T&)"], [68, 70])
      , (56, makeInputSet ["exc"], [6])
      , (58, makeInputSet ["call", "std::destroy<T>()"], [61])
      , (61, makeInputSet ["call", "T", "T::~T()"], [74])
      , (65, makeInputSet ["exc"], [6])
      , (68, makeInputSet ["exc"], [6])
      ]
  , eoDeltaShift =
      [ (8, makeInputSet ["ret", "Stack", "StackImpl::StackImpl(size_t)"], [9])
      , (10, makeInputSet ["ret", "::operator new()"], [11])
      , (12, makeInputSet ["exc"], [13])
      , (14, makeInputSet ["ret", "::operator delete()"], [15])
      , (18, makeInputSet ["ret", "Stack", "StackImpl::~StackImpl()"], [19])
      , (21, makeInputSet ["ret", "Stack", "Stack::Stack()"], [22])
      , (26, makeInputSet ["ret", "Stack", "StackImpl::Swap(StackImpl<T>&)", "tainted"], [27])
      , (28, makeInputSet ["ret", "Stack", "Stack::Size() const"], [29])
      , (32, makeInputSet ["ret", "Stack", "Stack::Stack(const Stack<T>&)"], [33])
      , (36, makeInputSet ["ret", "Stack", "Stack::operator=(const Stack<T>&)"], [76])
      , (38, makeInputSet ["ret", "Stack", "Stack::~Stack()"], [39])
      , (46, makeInputSet ["ret", "Stack", "Stack::Push(const T&)", "tainted"], [47])
      , (49, makeInputSet ["exc"], [50])
      , (51, makeInputSet ["exc"], [52])
      , (54, makeInputSet ["ret", "Stack", "Stack::Top() const"], [55])
      , (56, makeInputSet ["exc"], [57])
      , (59, makeInputSet ["ret", "Stack", "Stack::Pop()", "tainted"], [60])
      , (62, makeInputSet ["ret", "std::destroy<T>()"], [63])
      , (64, makeInputSet ["ret", "T", "T::T()"], [66])
      , (65, makeInputSet ["exc"], [67])
      , (69, makeInputSet ["exc"], [69])
      , (70, makeInputSet ["ret", "T", "T::T(const T&)"], [71])
      , (72, makeInputSet ["ret", "std::swap()", "tainted"], [73])
      , (74, makeInputSet ["ret", "T", "T::~T()"], [75])
      ]
  , eoDeltaPop =
      [ (6, 12, [6])
      , (6, 49, [6])
      , (6, 51, [6])
      , (6, 56, [6])
      , (6, 65, [6])
      , (6, 68, [6])
      , (9, 20, [21])
      , (9, 30, [31])
      , (11, 7, [8])
      , (12, 7, [12])
      , (15, 17, [21])
      , (19, 37, [38])
      , (19, 48, [49])
      , (22, 0, [1])
      , (27, 35, [36])
      , (27, 44, [46])
      , (29, 3, [4])
      , (33, 34, [35])
      , (33, 40, [41])
      , (39, 5, [6])
      , (47, 1, [2])
      , (47, 2, [3])
      , (49, 1, [49])
      , (49, 2, [49])
      , (56, 4, [56])
      , (60, 4, [5])
      , (63, 16, [17])
      , (63, 58, [59])
      , (68, 1, [68])
      , (68, 2, [68])
      , (68, 31, [68])
      , (68, 34, [68])
      , (68, 40, [68])
      , (68, 42, [68])
      , (68, 43, [68])
      , (68, 45, [68])
      , (68, 53, [68])
      , (69, 41, [48])
      , (71, 31, [31, 32])
      , (71, 42, [42, 43])
      , (71, 43, [44])
      , (71, 45, [46])
      , (71, 53, [54])
      , (73, 23, [24])
      , (73, 24, [25])
      , (73, 25, [26])
      , (75, 61, [62])
      , (75, 58, [59])
      ]
  }


slowTests :: TestTree
slowTests = testGroup "ModelChecking.hs Slow Tests" [lRSlowTests]

lRSlowTests :: TestTree
lRSlowTests = testGroup "LargerRec OPA MC Slow Tests" $
  map (makeTestCase largerRec) [(formulas !! 18, False), (formulas !! 44, False)]

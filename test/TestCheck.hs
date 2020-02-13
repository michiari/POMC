module TestCheck (tests) where

import Test.Tasty
import Test.Tasty.HUnit

import Data.Set (Set)
import qualified Data.Set as S

import POMC.Check
import POMC.Opa (Prec(..))
import POMC.Potl (Formula(..), Prop(..))

-- Each test is a tuple of the type:
-- (name, expected check result, phi, props, prec, input)

testTuples =
  [ ( "Test 1 (stack trace language)" -- Accepting predicate on first word position
    , True
    , And (Atomic $ Prop "call") (Not $ Atomic $ Prop "ret")
    , [Prop "call", Prop "ret"]
    , \s1 s2 -> if (Prop "call") `S.member` s1 then Equal else Take
    , [S.singleton (Prop "call"), S.singleton (Prop "ret")]
    )
  , ( "Test 2 (stack trace language)" -- Rejecting predicate on first word position
    , False
    , Atomic $ Prop "ret"
    , [Prop "call", Prop "ret"]
    , \s1 s2 -> if (Prop "call") `S.member` s1 then Equal else Take
    , [S.singleton (Prop "call"), S.singleton (Prop "ret")]
    )
  , ( "Test 3 (stack trace language)" -- Accepting PrecNext
    , True
    , PrecNext (S.singleton Equal) (Atomic $ Prop "ret")
    , [Prop "call", Prop "ret"]
    , \s1 s2 -> if (Prop "call") `S.member` s1 then Equal else Take
    , [S.singleton (Prop "call"), S.singleton (Prop "ret")]
    )
  , ( "Test 4 (stack trace language)" -- Rejecting PrecNext
    , False
    , PrecNext (S.singleton Equal) (Atomic $ Prop "call")
    , [Prop "call", Prop "ret"]
    , \s1 s2 -> if (Prop "call") `S.member` s1 then Equal else Take
    , [S.singleton (Prop "call"), S.singleton (Prop "ret")]
    )
  , ( "Test 5 (stack trace language)" -- OOB PrecNext is rejected
    , False
    , PrecNext (S.singleton Equal) (PrecNext (S.singleton Take) (Atomic $ Prop "call"))
    , [Prop "call", Prop "ret"]
    , \s1 s2 -> if (Prop "call") `S.member` s1 then Equal else Take
    , [S.singleton (Prop "call"), S.singleton (Prop "ret")]
    )
  , ( "Test 6 (stack trace language)" -- Accepting PrecBack
    , True
    , PrecNext (S.singleton Equal) (PrecBack (S.singleton Equal) (Atomic $ Prop "call"))
    , [Prop "call", Prop "ret"]
    , \s1 s2 -> if (Prop "call") `S.member` s1 then Equal else Take
    , [S.singleton (Prop "call"), S.singleton (Prop "ret")]
    )
  , ( "Test 7 (stack trace language)" -- Rejecting PrecBack
    , False
    , PrecNext (S.singleton Equal) (PrecBack (S.fromList [Yield, Take]) (Atomic $ Prop "call"))
    , [Prop "call", Prop "ret"]
    , \s1 s2 -> if (Prop "call") `S.member` s1 then Equal else Take
    , [S.singleton (Prop "call"), S.singleton (Prop "ret")]
    )
  ]

tests :: TestTree
tests = testGroup "Check.hs tests" (map makeTestCase testTuples)
  where acceptFail = "Formula should hold for given word!"
        rejectFail = "Formula should not hold for given word!"
        makeTestCase (name, expected, phi, props, prec, ts) =
          if expected == True
            then testCase name $ check phi props prec ts @? acceptFail
            else testCase name $ not (check phi props prec ts) @? rejectFail

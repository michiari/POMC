module TestCheck (tests) where

import Pomc.Check (fastcheckGen, fastcheck)
import Pomc.Example (stlPrecRelV1, stlAnnotateV1, stlPrecRelV2)
import Pomc.Prec (Prec(..))
import qualified Pomc.Prec as PS (singleton, fromList)
import Pomc.Prop (Prop(..))
import Pomc.PotlV2(Dir(..), Formula(..), formulaAt, formulaAfter)

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck

import qualified Data.Set as S

import Control.Monad

tests :: TestTree
tests = testGroup "Check.hs tests" [unitTests]

unitTests :: TestTree
unitTests = testGroup "Unit tests" [potlv2Tests1]
  where
    -- Takes a list of tuples like:
    --   (name, expected check result, checkable phi, prec func, input)
    makeTestCase (name, expected, phi, prec, ts) =
      case expected of
        False -> testCase name $ not (fastcheckGen phi prec ts) @? rejectFail
        True  -> testCase name $      fastcheckGen phi prec ts  @? acceptFail
      where acceptFail = "Formula should hold for given word!"
            rejectFail = "Formula should not hold for given word!"

    potlv2Tests1 = testGroup "POTL, Stack Trace Lang V1, first group test" $ map makeTestCase
      [ ( "Accepting Always"
        , True
        , Always . Atomic . Prop $ "call"
        , stlPrecRelV2
        , map (S.singleton . Prop) ["call", "call", "call"]
        )
      , ( "Accepting XBack Down through the Yield relation" 
        , True
        , formulaAfter [Down, Up] $ XBack Down (Atomic $ Prop "han")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["han", "call", "thr"]
        )
      , ( "Accepting XNext Down" 
        , True
        , XNext Down (Atomic $ Prop "ret")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "han", "ret"]
        )
      , ( "Rejecting Not XBack Down through the Yield relation"
        , False
        , formulaAfter [Down, Up] $ Not (XBack Down (Atomic $ Prop "han"))
        , stlPrecRelV1
        , map (S.singleton . Prop) ["han", "call", "thr"]
        )
      , ( "Accepting inner XBack Down"
        , True
        , formulaAfter [Down, Down, Up] $ XBack Down (Atomic $ Prop "han")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "han", "call", "thr", "ret"]
        )
      , ( "Rejecting XBack Down"
        , False
        , formulaAfter [Down, Up] $ XBack Down (Atomic $ Prop "han")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["han", "thr", "ret"]
        )
      , ( "Rejecting inner XBack Down"  
        , False
        , formulaAfter  [Down, Up, Up] $ XBack Down (Atomic $ Prop "call")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["han", "call", "thr", "thr", "ret"]
        )
      , ( "Rejecting inner XBack Down -- v2" 
        , False
        , formulaAfter [Down, Down, Up] $ XBack Down (Atomic $ Prop "han")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "han", "thr", "ret", "ret"]
        )
      , ( "Accepting XBack Down through the Equal relation" 
        , True
        , formulaAfter [Down, Up] $ XBack Down (Atomic $ Prop "call")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "han", "ret"]
        )
      , ( "Rejecting Not XBack Down through the Equal relation" 
        , False
        , formulaAfter [Down, Up] $ Not (XBack Down (Atomic $ Prop "call"))
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "han", "ret"]
        )
      , ( "Accepting inner XBack Down through Equal relation" 
        , True
        , formulaAfter [Down, Down, Up] $ XBack Down (Atomic $ Prop "call")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "call", "han", "ret", "ret"]
        )
      , ( "Accepting XBack Up" 
        , True
        , formulaAfter [Down, Up] $ XBack Up (Atomic $ Prop "han")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["han", "thr", "ret"]
        )
      , ( "Rejecting Not XBack Up"
        , False
        , formulaAfter [Down, Up] $ Not (XBack Up (Atomic $ Prop "han"))
        , stlPrecRelV1
        , map (S.singleton . Prop) ["han", "thr", "ret"]
        )
      , ( "Rejecting XBack Up"
        , False
        , formulaAfter [Down, Up] $ XBack Up (Atomic $ Prop "han")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["han", "call", "thr"]
        )
      , ( "Accepting inner XBack Up"
        , True
        , formulaAfter [Down, Down , Up] $ XBack Up (Atomic $ Prop "han")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "han", "thr", "ret", "ret"]
        )
      ]

    
propTests :: TestTree
propTests = testGroup "QuickCheck tests" (map makePropTest propTuples)
  where makePropTest (name, expected, phi, _, gen) =
          testProperty name $
            forAll (sized gen) $ \input -> fastcheckGen phi stlPrecRelV1 input == expected

        -- Each property test is a tuple of the type:
        -- (name, expected check result, phi, prec, generator)
        propTuples =
          [ ( "Well formed stack traces, all calls return"
            , True
            , Always $ (Atomic . Prop $ "call") `Implies` ((PNext Down . Atomic . Prop $ "ret") `Or` (XNext Down . Atomic . Prop $ "ret"))
            , stlPrecRelV1
            , \m -> map (S.singleton . Prop) <$> wellFormedTrace m
            )
          , ( "Well formed stack traces, all exceptions are handled"
            , True
            , Always $ (Atomic . Prop $ "thr") `Implies` ((PBack Down . Atomic . Prop $ "han") `Or` (XBack Down . Atomic . Prop $ "han"))
            , stlPrecRelV1
            , \m -> map (S.singleton . Prop) <$> wellFormedTrace m
            )
          ]

wellFormedTrace :: Int -> Gen [String]
wellFormedTrace m = return ["call"] `gconcat` (arb m) `gconcat` return ["ret"]
  where gconcat = liftM2 (++)
        arb 0 = return []
        arb l = do n <- choose (0, l `div` 2)
                   oneof [ return ["call"] `gconcat` (arb n) `gconcat` return ["ret"] `gconcat` (arb n)
                         , return ["han"]  `gconcat` (arb n) `gconcat` (arbStr "thr" 3) `gconcat` (arb n)
                         ]
        arbStr str l = do n <- choose (0, l)
                          return (replicate n str)

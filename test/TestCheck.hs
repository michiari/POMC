module TestCheck ( tests
                 , termTrace) where

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck

import Data.Set (Set)
import qualified Data.Set as S

import Control.Monad

import POMC.Check
import POMC.Opa (Prec(..))
import POMC.Potl (Formula(..), Prop(..), formulaAt)

stlPrec s1 s2
  | S.null s2 = Take -- Can happen with e.g. PrecNext checks
  | (Prop "call") `S.member` s1 = callPrec s2
  | (Prop  "ret") `S.member` s1 =  retPrec s2
  | (Prop  "han") `S.member` s1 =  hanPrec s2
  | (Prop  "thr") `S.member` s1 =  thrPrec s2
  | otherwise = error "Incompatible tokens"
  where callPrec s
          | (Prop "call") `S.member` s = Yield
          | (Prop  "ret") `S.member` s = Equal
          | (Prop  "han") `S.member` s = Yield
          | (Prop  "thr") `S.member` s = Take
          | otherwise = error "Incompatible tokens"
        retPrec s
          | (Prop "call") `S.member` s = Take
          | (Prop  "ret") `S.member` s = Take
          | (Prop  "han") `S.member` s = Yield
          | (Prop  "thr") `S.member` s = Take
          | otherwise = error "Incompatible tokens"
        hanPrec s
          | (Prop "call") `S.member` s = Yield
          | (Prop  "ret") `S.member` s = Take
          | (Prop  "han") `S.member` s = Yield
          | (Prop  "thr") `S.member` s = Yield
          | otherwise = error "Incompatible tokens"
        thrPrec s
          | (Prop "call") `S.member` s = Take
          | (Prop  "ret") `S.member` s = Take
          | (Prop  "han") `S.member` s = Take
          | (Prop  "thr") `S.member` s = Take
          | otherwise = error "Incompatible tokens"

-- Each unit test is a tuple of the type:
-- (name, expected check result, phi, prec, input)
unitTuples =
  [ ( "Stack trace lang, accepting predicate on first word position"
    , True
    , And (Atomic $ Prop "call") (Not $ Atomic $ Prop "ret")
    , stlPrec
    , map (S.singleton . Prop) ["call", "ret"]
    )
  , ( "Stack trace lang, rejecting predicate on first word position"
    , False
    , Atomic $ Prop "ret"
    , stlPrec
    , map (S.singleton . Prop) ["call", "ret"]
    )
  , ( "Stack trace lang, accepting PrecNext"
    , True
    , PrecNext (S.singleton Equal) (Atomic $ Prop "ret")
    , stlPrec
    , map (S.singleton . Prop) ["call", "ret"]
    )
  , ( "Stack trace lang, rejecting PrecNext"
    , False
    , PrecNext (S.singleton Equal) (Atomic $ Prop "call")
    , stlPrec
    , map (S.singleton . Prop) ["call", "ret"]
    )
  , ( "Stack trace lang, rejecting OOB PrecNext"
    , False
    , PrecNext (S.singleton Equal) (PrecNext (S.singleton Take) (Atomic $ Prop "call"))
    , stlPrec
    , map (S.singleton . Prop) ["call", "ret"]
    )
  , ( "Stack trace lang, accepting PrecBack"
    , True
    , PrecNext (S.singleton Equal) (PrecBack (S.singleton Equal) (Atomic $ Prop "call"))
    , stlPrec
    , map (S.singleton . Prop) ["call", "ret"]
    )
  , ( "Stack trace lang, rejecting PrecBack"
    , False
    , PrecNext (S.singleton Equal) (PrecBack (S.fromList [Yield, Take]) (Atomic $ Prop "call"))
    , stlPrec
    , map (S.singleton . Prop) ["call", "ret"]
    )
  , ( "Stack trace lang, rejecting OOB PrecBack"
    , False
    , PrecBack (S.fromList [Yield, Equal, Take]) (Atomic $ Prop "call")
    , stlPrec
    , map (S.singleton . Prop) ["call", "ret"]
    )
  , ( "Stack trace lang, rejecting OOB PrecBack"
    , False
    , PrecBack (S.fromList [Yield, Equal, Take]) $ PrecBack (S.fromList [Yield, Equal, Take]) (Atomic $ Prop "call")
    , stlPrec
    , map (S.singleton . Prop) ["call", "ret"]
    )
  , ( "Stack trace lang, accepting ChainNext Equal"
    , True
    , ChainNext (S.singleton Equal) (Atomic $ Prop "ret")
    , stlPrec
    , map (S.singleton . Prop) ["call", "han", "ret"]
    )
  , ( "Stack trace lang, rejecting ChainNext Equal"
    , False
    , ChainNext (S.singleton Equal) (Atomic $ Prop "ret")
    , stlPrec
    , map (S.singleton . Prop) ["han", "thr", "ret"]
    )
  , ( "Stack trace lang, accepting inner ChainNext Equal"
    , True
    , PrecNext (S.fromList [Yield, Equal, Take]) $ ChainNext (S.singleton Equal) (Atomic $ Prop "ret")
    , stlPrec
    , map (S.singleton . Prop) ["call", "call", "han", "ret", "ret"]
    )
  , ( "Stack trace lang, rejecting inner ChainNext Equal"
    , False
    , PrecNext (S.fromList [Yield, Equal, Take]) $ ChainNext (S.singleton Equal) (Atomic $ Prop "ret")
    , stlPrec
    , map (S.singleton . Prop) ["call", "han", "thr", "ret", "ret"]
    )
  , ( "Stack trace lang, accepting ChainNext Take"
    , True
    , ChainNext (S.singleton Take) (Atomic $ Prop "ret")
    , stlPrec
    , map (S.singleton . Prop) ["han", "thr", "ret"]
    )
  , ( "Stack trace lang, rejecting ChainNext Take"
    , False
    , ChainNext (S.singleton Take) (Atomic $ Prop "ret")
    , stlPrec
    , map (S.singleton . Prop) ["call", "han", "ret"]
    )
  , ( "Stack trace lang, accepting inner ChainNext Take"
    , True
    , PrecNext (S.fromList [Yield, Equal, Take]) $ ChainNext (S.singleton Take) (Atomic $ Prop "ret")
    , stlPrec
    , map (S.singleton . Prop) ["call", "han", "thr", "ret"]
    )
  , ( "Stack trace lang, rejecting inner ChainNext Take"
    , False
    , PrecNext (S.fromList [Yield, Equal, Take]) $ ChainNext (S.singleton Take) (Atomic $ Prop "ret")
    , stlPrec
    , map (S.singleton . Prop) ["call", "call", "han", "thr", "ret", "ret"]
    )
  , ( "Stack trace lang, accepting ChainNext Yield"
    , True
    , ChainNext (S.singleton Yield) (Atomic $ Prop "thr")
    , stlPrec
    , map (S.singleton . Prop) ["han", "call", "thr"]
    )
  , ( "Stack trace lang, rejecting ChainNext Yield"
    , False
    , ChainNext (S.singleton Yield) (Atomic $ Prop "ret")
    , stlPrec
    , map (S.singleton . Prop) ["call", "han", "ret"]
    )
  , ( "Stack trace lang, accepting inner ChainNext Yield"
    , True
    , PrecNext (S.fromList [Yield, Equal, Take]) $ ChainNext (S.singleton Yield) (Atomic $ Prop "thr")
    , stlPrec
    , map (S.singleton . Prop) ["call", "han", "call", "call", "call", "thr", "thr", "thr", "ret"]
    )
  , ( "Stack trace lang, rejecting inner ChainNext Yield"
    , False
    , PrecNext (S.fromList [Yield, Equal, Take]) $ ChainNext (S.singleton Yield) (Atomic $ Prop "ret")
    , stlPrec
    , map (S.singleton . Prop) ["call", "han", "call", "call", "call", "thr", "thr", "thr", "ret"]
    )
  , ( "Stack trace lang, accepting ChainNext YTE through ChainNext Equal"
    , True
    , ChainNext (S.fromList [Yield, Equal, Take]) (Atomic $ Prop "ret")
    , stlPrec
    , map (S.singleton . Prop) ["call", "han", "ret"]
    )
  , ( "Stack trace lang, accepting ChainNext YTE through ChainNext Yield"
    , True
    , ChainNext (S.fromList [Yield, Equal, Take]) (Atomic $ Prop "thr")
    , stlPrec
    , map (S.singleton . Prop) ["han", "call", "thr"]
    )
  , ( "Stack trace lang, accepting ChainNext YTE through ChainNext Take"
    , True
    , ChainNext (S.fromList [Yield, Equal, Take]) (Atomic $ Prop "ret")
    , stlPrec
    , map (S.singleton . Prop) ["han", "thr", "ret"]
    )
  , ( "Stack trace lang, rejecting ChainNext YTE"
    , False
    , ChainNext (S.fromList [Yield, Equal, Take]) (Atomic $ Prop "ret")
    , stlPrec
    , map (S.singleton . Prop) ["call", "ret"] -- there is no inner chain ;)
    )
  , ( "Stack trace lang, rejecting ChainNext YT"
    , False
    , ChainNext (S.fromList [Yield, Take]) (Atomic $ Prop "ret")
    , stlPrec
    , map (S.singleton . Prop) ["call", "han", "ret"]
    )
  , ( "Stack trace lang, rejecting ChainNext ET"
    , False
    , ChainNext (S.fromList [Equal, Take]) (Atomic $ Prop "ret")
    , stlPrec
    , map (S.singleton . Prop) ["han", "call", "thr"]
    )
  , ( "Stack trace lang, rejecting ChainNext YE"
    , False
    , ChainNext (S.fromList [Yield, Equal]) (Atomic $ Prop "ret")
    , stlPrec
    , map (S.singleton . Prop) ["han", "thr", "ret"]
    )
  , ( "Stack trace lang, accepting Until Y"
    , True
    , Until (S.singleton Yield) (Not . Atomic . Prop $ "thr") (Atomic $ Prop "han")
    , stlPrec
    , map (S.singleton . Prop) ["call", "call", "han", "thr", "ret", "ret"]
    )
  , ( "Stack trace lang, rejecting Until Y"
    , False
    , Until (S.singleton Yield) (Not . Atomic . Prop $ "han") (Atomic $ Prop "thr")
    , stlPrec
    , map (S.singleton . Prop) ["call", "call", "han", "thr", "ret", "ret"]
    )
  , ( "Stack trace lang, accepting Until YET"
    , True
    , Until (S.fromList [Yield, Equal, Take]) (Not . Atomic . Prop $ "thr") (Atomic $ Prop "han")
    , stlPrec
    , map (S.singleton . Prop) ["call", "call", "han", "thr", "ret", "ret"]
    )
  , ( "Stack trace lang, accepting ChainBack Equal"
    , True
    , formulaAt 3 $ ChainBack (S.singleton Equal) (Atomic $ Prop "call")
    , stlPrec
    , map (S.singleton . Prop) ["call", "han", "ret"]
    )
  , ( "Stack trace lang, rejecting ChainBack Equal"
    , False
    , formulaAt 3 $ ChainBack (S.singleton Equal) (Atomic $ Prop "han")
    , stlPrec
    , map (S.singleton . Prop) ["han", "thr", "ret"]
    )
  , ( "Stack trace lang, accepting inner ChainBack Equal"
    , True
    , formulaAt 4 $ ChainBack (S.singleton Equal) (Atomic $ Prop "call")
    , stlPrec
    , map (S.singleton . Prop) ["call", "call", "han", "ret", "ret"]
    )
  , ( "Stack trace lang, rejecting inner ChainBack Equal"
    , False
    , formulaAt 4 $ ChainBack (S.singleton Equal) (Atomic $ Prop "han")
    , stlPrec
    , map (S.singleton . Prop) ["call", "han", "thr", "ret", "ret"]
    )
  , ( "Stack trace lang, accepting ChainBack Yield"
    , True
    , formulaAt 3 $ ChainBack (S.singleton Yield) (Atomic $ Prop "han")
    , stlPrec
    , map (S.singleton . Prop) ["han", "call", "thr"]
    )
  , ( "Stack trace lang, rejecting ChainBack Yield"
    , False
    , formulaAt 3 $ ChainBack (S.singleton Yield) (Atomic $ Prop "call")
    , stlPrec
    , map (S.singleton . Prop) ["call", "han", "ret"]
    )
  , ( "Stack trace lang, accepting inner ChainBack Yield"
    , True
    , formulaAt 4 $ ChainBack (S.singleton Yield) (Atomic $ Prop "han")
    , stlPrec
    , map (S.singleton . Prop) ["call", "han", "call", "thr", "ret"]
    )
  , ( "Stack trace lang, rejecting inner ChainBack Yield"
    , False
    , formulaAt 4 $ ChainBack (S.singleton Yield) (Atomic $ Prop "call")
    , stlPrec
    , map (S.singleton . Prop) ["call", "call", "han", "ret", "ret"]
    )
  , ( "Stack trace lang, accepting ChainBack Take"
    , True
    , formulaAt 3 $ ChainBack (S.singleton Take) (Atomic $ Prop "han")
    , stlPrec
    , map (S.singleton . Prop) ["han", "thr", "ret"]
    )
  , ( "Stack trace lang, rejecting ChainBack Take"
    , False
    , formulaAt 3 $ ChainBack (S.singleton Take) (Atomic $ Prop "call")
    , stlPrec
    , map (S.singleton . Prop) ["call", "han", "ret"]
    )
  , ( "Stack trace lang, accepting inner ChainBack Take"
    , True
    , formulaAt 4 $ ChainBack (S.singleton Take) (Atomic $ Prop "han")
    , stlPrec
    , map (S.singleton . Prop) ["call", "han", "thr", "ret"]
    )
  , ( "Stack trace lang, rejecting inner ChainBack Take"
    , False
    , formulaAt 4 $ ChainBack (S.singleton Take) (Atomic $ Prop "call")
    , stlPrec
    , map (S.singleton . Prop) ["call", "call", "han", "thr", "ret", "ret"]
    )
  ]

unitTests = testGroup "Unit" (map makeTestCase unitTuples)
  where acceptFail = "Formula should hold for given word!"
        rejectFail = "Formula should not hold for given word!"
        makeTestCase (name, expected, phi, prec, ts) =
          if expected == True
            then testCase name $ check phi prec ts @? acceptFail
            else testCase name $ not (check phi prec ts) @? rejectFail

termTrace :: Int -> Gen [String]
termTrace m = return ["call"] `gconcat` (arb m) `gconcat` return ["ret"]
  where gconcat = liftM2 (++)
        arb 0 = return []
        arb m = do n <- choose (0, m `div` 2)
                   oneof [ return ["call"] `gconcat` (arb n) `gconcat` return ["ret"] `gconcat` (arb n)
                         , return ["han"]  `gconcat` (arb n) `gconcat` (arbStr "thr" 3) `gconcat` (arb n)
                         ]
        arbStr str m = do n <- choose (0, m)
                          return (replicate n str)

-- Each property test is a tuple of the type:
-- (name, expected check result, phi, prec, generator)
propTuples =
  [ ( "Well formed stack traces"
    , True
    , (Atomic . Prop $ "call") `And` ((PrecNext (S.singleton Equal) (Atomic . Prop $ "ret")) `Or` (ChainNext (S.singleton Equal) (Atomic . Prop $ "ret")))
    , stlPrec
    , \m -> map (S.singleton . Prop) <$> termTrace m
    )
  , ( "Well formed stack traces, no throw before handle"
    , True
    , Until (S.fromList [Yield, Equal, Take]) (Not . Atomic . Prop $ "thr") (Atomic $ Prop "han")
    , stlPrec
    , \m -> map (S.singleton . Prop) <$> termTrace m
    )
  ]

properties :: TestTree
properties = testGroup "QuickCheck tests" (map makePropTest propTuples)
  where makePropTest (name, expected, phi, prec, gen) =
          testProperty name $
            forAll (sized gen) $ \input -> check phi stlPrec input == expected

tests :: TestTree
tests = testGroup "Check.hs tests" [unitTests, properties]

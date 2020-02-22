module TestCheck (tests) where

import Test.Tasty
import Test.Tasty.HUnit

import Data.Set (Set)
import qualified Data.Set as S

import POMC.Check
import POMC.Opa (Prec(..))
import POMC.Potl (Formula(..), Prop(..))

stlPrec s1 s2
  | null s2 = Take -- Can happen with e.g. PrecNext checks
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

-- Each test is a tuple of the type:
-- (name, expected check result, phi, props, prec, input)
testTuples =
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
  , ( "Stack trace lang, OOB PrecNext is rejected"
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
  , ( "Stack trace lang, OOB PrecBack is rejected"
    , False
    , PrecBack (S.fromList [Yield, Equal, Take]) (Atomic $ Prop "call")
    , stlPrec
    , map (S.singleton . Prop) ["call", "ret"]
    )
  , ( "Stack trace lang, OOB PrecBack is rejected"
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
    , ChainNext (S.singleton Equal) (Atomic $ Prop "han")
    , stlPrec
    , map (S.singleton . Prop) ["call", "han", "ret"]
    )
  , ( "Stack trace lang, accepting inner ChainNext Equal"
    , True
    , PrecNext (S.fromList [Yield, Equal, Take]) $ ChainNext (S.singleton Equal) (Atomic $ Prop "ret")
    , stlPrec
    , map (S.singleton . Prop) ["call", "call", "han", "ret", "ret"]
    )
  -- Takes slightly longer
  , ( "Stack trace lang, rejecting inner ChainNext Equal"
    , False
    , PrecNext (S.fromList [Yield, Equal, Take]) $ ChainNext (S.singleton Equal) (Atomic $ Prop "call")
    , stlPrec
    , map (S.singleton . Prop) ["call", "call", "han", "ret", "ret"]
    )
  , ( "Stack trace lang, accepting ChainNext Yield"
    , True
    , ChainNext (S.singleton Yield) (Atomic $ Prop "thr")
    , stlPrec
    , map (S.singleton . Prop) ["han", "call", "thr"]
    )
  , ( "Stack trace lang, accepting inner ChainNext Yield"
    , True
    , PrecNext (S.fromList [Yield, Equal, Take]) $ ChainNext (S.singleton Yield) (Atomic $ Prop "thr")
    , stlPrec
    , map (S.singleton . Prop) ["call", "han", "call", "call", "call", "thr", "thr", "thr", "ret"]
    )
  , ( "Stack trace lang, rejecting ChainNext Yield"
    , False
    , ChainNext (S.singleton Yield) (Atomic $ Prop "ret")
    , stlPrec
    , map (S.singleton . Prop) ["call", "han", "ret"]
    )
  -- Takes slightly longer
  , ( "Stack trace lang, rejecting inner ChainNext Yield"
    , False
    , PrecNext (S.fromList [Yield, Equal, Take]) $ ChainNext (S.singleton Yield) (Atomic $ Prop "ret")
    , stlPrec
    , map (S.singleton . Prop) ["call", "han", "call", "call", "call", "thr", "thr", "thr", "ret"]
    )
  , ( "Stack trace lang, accepting Until YET"
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
  ]

tests :: TestTree
tests = testGroup "Check.hs tests" (map makeTestCase testTuples)
  where acceptFail = "Formula should hold for given word!"
        rejectFail = "Formula should not hold for given word!"
        makeTestCase (name, expected, phi, prec, ts) =
          if expected == True
            then testCase name $ check phi prec ts @? acceptFail
            else testCase name $ not (check phi prec ts) @? rejectFail

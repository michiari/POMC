module TestCheck (tests) where

import Pomc.Check (fastcheckGen)
import Pomc.Example (stlPrecRelV1, stlAnnotateV1, stlPrecRelV2)
import Pomc.Prec (Prec(..))
import qualified Pomc.Prec as PS (singleton, fromList)
import Pomc.Prop (Prop(..))
import Pomc.RPotl (Formula(..), formulaAt)
import qualified Pomc.PotlV2 as P2 (Dir(..), Formula(..))

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck

import qualified Data.Set as S

import Control.Monad

tests :: TestTree
tests = testGroup "Check.hs tests" [unitTests, propTests]

unitTests :: TestTree
unitTests = testGroup "Unit tests" [rpotlTests, potlv2Tests]
  where
    -- Takes a list of tuples like:
    --   (name, expected check result, checkable phi, prec func, input)
    makeTestCase (name, expected, phi, prec, ts) =
      case expected of
        False -> testCase name $ not (fastcheckGen phi prec ts) @? rejectFail
        True  -> testCase name $       fastcheckGen phi prec ts @? acceptFail
      where acceptFail = "Formula should hold for given word!"
            rejectFail = "Formula should not hold for given word!"

    rpotlTests = testGroup "RPotl, Stack Trace Lang V1" $ map makeTestCase
      [ ( "Accepting predicate on first word position"
        , True
        , Atomic . Prop  $ "call"
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "ret"]
        )
      , ( "Rejecting Not predicate on first word position"
        , False
        , Not (Atomic . Prop  $ "call")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "ret"]
        )
      , ( "Accepting Not"
        , True
        , Not . Atomic . Prop  $ "ret"
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "ret"]
        )
      , ( "Rejecting Not Not"
        , False
        , Not . Not . Atomic . Prop  $ "ret"
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "ret"]
        )
      , ( "Rejecting Not"
        , False
        , Not . Atomic . Prop  $ "call"
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "ret"]
        )
      , ( "Accepting multiple negation"
        , True
        , Not . Not . Not . Not . Atomic . Prop  $ "call"
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "ret"]
        )
      , ( "Rejecting multiple negation"
        , False
        , Not . Not . Not . Not . Not . Atomic . Prop  $ "call"
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "ret"]
        )
      , ( "Accepting And"
        , True
        , And (Atomic $ Prop "call") (Not $ Atomic $ Prop "ret")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "ret"]
        )
      , ( "Rejecting Not And"
        , False
        , Not (And (Atomic $ Prop "call") (Not $ Atomic $ Prop "ret"))
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "ret"]
        )
      , ( "Accepting Or"
        , True
        , Or (Atomic . Prop $ "call") (Atomic . Prop $ "ret")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "ret"]
        )
      , ( "Rejecting Not Or"
        , False
        , Not (Or (Atomic . Prop $ "call") (Atomic . Prop $ "ret"))
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "ret"]
        )
      , ( "Accepting PrecNext"
        , True
        , PrecNext (PS.singleton Equal) (Atomic $ Prop "ret")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "ret"]
        )
      , ( "Rejecting Not PrecNext"
        , False
        , Not $ PrecNext (PS.singleton Equal) (Atomic $ Prop "ret")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "ret"]
        )
      , ( "Rejecting PrecNext"
        , False
        , PrecNext (PS.singleton Equal) (Atomic $ Prop "call")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "ret"]
        )
      , ( "Rejecting OOB PrecNext"
        , False
        , PrecNext (PS.singleton Equal) (PrecNext (PS.singleton Take) (Atomic $ Prop "call"))
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "ret"]
        )
      , ( "Accepting PrecBack"
        , True
        , PrecNext (PS.singleton Equal) (PrecBack (PS.singleton Equal) (Atomic $ Prop "call"))
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "ret"]
        )
      , ( "Rejecting Not PrecBack"
        , False
        , PrecNext (PS.singleton Equal) $ Not (PrecBack (PS.singleton Equal) (Atomic $ Prop "call"))
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "ret"]
        )
      , ( "Rejecting PrecBack"
        , False
        , PrecNext (PS.singleton Equal) (PrecBack (PS.fromList [Yield, Take]) (Atomic $ Prop "call"))
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "ret"]
        )
      , ( "Rejecting OOB PrecBack"
        , False
        , PrecBack (PS.fromList [Yield, Equal, Take]) (Atomic $ Prop "call")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "ret"]
        )
      , ( "Rejecting OOB PrecBack"
        , False
        , PrecBack (PS.fromList [Yield, Equal, Take]) $ PrecBack (PS.fromList [Yield, Equal, Take]) (Atomic $ Prop "call")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "ret"]
        )
      , ( "Accepting ChainNext Yield"
        , True
        , ChainNext (PS.singleton Yield) (Atomic $ Prop "thr")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["han", "call", "thr"]
        )
      , ( "Rejecting Not ChainNext Yield"
        , False
        , Not $ ChainNext (PS.singleton Yield) (Atomic $ Prop "thr")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["han", "call", "thr"]
        )
      , ( "Rejecting ChainNext Yield"
        , False
        , ChainNext (PS.singleton Yield) (Atomic $ Prop "ret")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "han", "ret"]
        )
      , ( "Accepting inner ChainNext Yield"
        , True
        , PrecNext (PS.fromList [Yield, Equal, Take]) $ ChainNext (PS.singleton Yield) (Atomic $ Prop "thr")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "han", "call", "thr", "ret"]
        )
      , ( "Rejecting inner ChainNext Yield"
        , False
        , PrecNext (PS.fromList [Yield, Equal, Take]) $ ChainNext (PS.singleton Yield) (Atomic $ Prop "ret")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "han", "call", "thr", "ret"]
        )
      , ( "Push after pop with ChainNext Yield in closure"
        , True
        , Or (ChainNext (PS.singleton Yield) (Atomic $ Prop "call")) (Atomic $ Prop "call")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "ret", "call", "ret"]
        )
      , ( "Accepting ChainNext Equal"
        , True
        , ChainNext (PS.singleton Equal) (Atomic $ Prop "ret")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "han", "ret"]
        )
      , ( "Rejecting Not ChainNext Equal"
        , False
        , Not $ ChainNext (PS.singleton Equal) (Atomic $ Prop "ret")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "han", "ret"]
        )
      , ( "Rejecting ChainNext Equal"
        , False
        , ChainNext (PS.singleton Equal) (Atomic $ Prop "ret")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["han", "thr", "ret"]
        )
      , ( "Accepting inner ChainNext Equal"
        , True
        , PrecNext (PS.fromList [Yield, Equal, Take]) $ ChainNext (PS.singleton Equal) (Atomic $ Prop "ret")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "call", "han", "ret", "ret"]
        )
      , ( "Rejecting inner ChainNext Equal"
        , False
        , PrecNext (PS.fromList [Yield, Equal, Take]) $ ChainNext (PS.singleton Equal) (Atomic $ Prop "ret")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "han", "thr", "ret", "ret"]
        )
      , ( "Accepting ChainNext Take"
        , True
        , ChainNext (PS.singleton Take) (Atomic $ Prop "ret")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["han", "thr", "ret"]
        )
      , ( "Rejecting Not ChainNext Take"
        , False
        , Not $ ChainNext (PS.singleton Take) (Atomic $ Prop "ret")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["han", "thr", "ret"]
        )
      , ( "Rejecting ChainNext Take"
        , False
        , ChainNext (PS.singleton Take) (Atomic $ Prop "ret")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "han", "ret"]
        )
      , ( "Accepting inner ChainNext Take"
        , True
        , PrecNext (PS.fromList [Yield, Equal, Take]) $ ChainNext (PS.singleton Take) (Atomic $ Prop "ret")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "han", "thr", "ret"]
        )
      , ( "Rejecting inner ChainNext Take"
        , False
        , PrecNext (PS.fromList [Yield, Equal, Take]) $ ChainNext (PS.singleton Take) (Atomic $ Prop "ret")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "call", "han", "thr", "ret", "ret"]
        )
      , ( "Accepting ChainNext YET through ChainNext Equal"
        , True
        , ChainNext (PS.fromList [Yield, Equal, Take]) (Atomic $ Prop "ret")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "han", "ret"]
        )
      , ( "Accepting ChainNext YET through ChainNext Yield"
        , True
        , ChainNext (PS.fromList [Yield, Equal, Take]) (Atomic $ Prop "thr")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["han", "call", "thr"]
        )
      , ( "Accepting ChainNext YET through ChainNext Take"
        , True
        , ChainNext (PS.fromList [Yield, Equal, Take]) (Atomic $ Prop "ret")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["han", "thr", "ret"]
        )
      , ( "Rejecting Not ChainNext YET through ChainNext Equal"
        , False
        , Not $ ChainNext (PS.fromList [Yield, Equal, Take]) (Atomic $ Prop "ret")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "han", "ret"]
        )
      , ( "Rejecting Not ChainNext YET through ChainNext Yield"
        , False
        , Not $ ChainNext (PS.fromList [Yield, Equal, Take]) (Atomic $ Prop "thr")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["han", "call", "thr"]
        )
      , ( "Rejecting Not ChainNext YET through ChainNext Take"
        , False
        , Not $ ChainNext (PS.fromList [Yield, Equal, Take]) (Atomic $ Prop "ret")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["han", "thr", "ret"]
        )
      , ( "Rejecting Not Or of ChainNext forumulas through ChainNext Take"
        , False
        , Not $ (Or (ChainNext (PS.singleton Yield) (Atomic $ Prop "ret")) (Or (ChainNext (PS.singleton Equal) (Atomic $ Prop "ret")) (ChainNext (PS.singleton Take) (Atomic $ Prop "ret"))))
        , stlPrecRelV1
        , map (S.singleton . Prop) ["han", "thr", "ret"]
        )
      , ( "Rejecting ChainNext YET"
        , False
        , ChainNext (PS.fromList [Yield, Equal, Take]) (Atomic $ Prop "ret")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "ret"] -- there is no inner chain ;)
        )
      , ( "Rejecting ChainNext YT"
        , False
        , ChainNext (PS.fromList [Yield, Take]) (Atomic $ Prop "ret")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "han", "ret"]
        )
      , ( "Rejecting ChainNext ET"
        , False
        , ChainNext (PS.fromList [Equal, Take]) (Atomic $ Prop "ret")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["han", "call", "thr"]
        )
      , ( "Rejecting ChainNext YE"
        , False
        , ChainNext (PS.fromList [Yield, Equal]) (Atomic $ Prop "ret")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["han", "thr", "ret"]
        )
      , ( "Accepting Until Y through ChainNext Yield"
        , True
        , Until (PS.singleton Yield) (Not . Atomic . Prop $ "call") (Atomic $ Prop "thr")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["han", "call", "thr"]
        )
      , ( "Rejecting Until Y"
        , False
        , Until (PS.singleton Yield) (Not . Atomic . Prop $ "han") (Atomic $ Prop "thr")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["han", "call", "thr"]
        )
      , ( "Accepting Until E through ChainNext Equal"
        , True
        , Until (PS.singleton Equal) (Not . Atomic . Prop $ "han") (Atomic $ Prop "ret")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "han", "ret"]
        )
      , ( "Rejecting Until E"
        , False
        , Until (PS.singleton Equal) (Not . Atomic . Prop $ "call") (Atomic $ Prop "ret")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "han", "ret"]
        )
      , ( "Accepting Until T through ChainNext Take"
        , True
        , Until (PS.singleton Take) (Not . Atomic . Prop $ "thr") (Atomic $ Prop "ret")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["han", "thr", "ret"]
        )
      , ( "Rejecting Until T"
        , False
        , Until (PS.singleton Take) (Not . Atomic . Prop $ "han") (Atomic $ Prop "ret")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["han", "thr", "ret"]
        )
      , ( "Accepting Until YET"
        , True
        , Until (PS.fromList [Yield, Equal, Take]) (Not . Atomic . Prop $ "ret") (Atomic $ Prop "han")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "han", "thr", "ret"]
        )
      , ( "Rejecting Not Until YET"
        , False
        , Not (Until (PS.fromList [Yield, Equal, Take]) (Not . Atomic . Prop $ "ret") (Atomic $ Prop "han"))
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "han", "thr", "ret"]
        )
      , ( "Accepting Until YET" -- this fails if the Until conditions for an atom
        , True                         -- are implemented with XOR instead of OR
        , Until (PS.fromList [Yield, Equal, Take]) (Not . Atomic . Prop $ "thr") (Atomic $ Prop "ret")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "han", "thr", "ret"]
        )
      , ( "Rejecting Not Until YET"
        , False
        , Not (Until (PS.fromList [Yield, Equal, Take]) (Not . Atomic . Prop $ "thr") (Atomic $ Prop "ret"))
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "han", "thr", "ret"]
        )
      , ( "Accepting ChainBack Yield"
        , True
        , formulaAt 3 $ ChainBack (PS.singleton Yield) (Atomic $ Prop "han")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["han", "call", "thr"]
        )
      , ( "Rejecting Not ChainBack Yield"
        , False
        , formulaAt 3 $ Not (ChainBack (PS.singleton Yield) (Atomic $ Prop "han"))
        , stlPrecRelV1
        , map (S.singleton . Prop) ["han", "call", "thr"]
        )
      , ( "Rejecting ChainBack Yield"
        , False
        , formulaAt 3 $ ChainBack (PS.singleton Yield) (Atomic $ Prop "call")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "han", "ret"]
        )
      , ( "Accepting inner ChainBack Yield"
        , True
        , formulaAt 4 $ ChainBack (PS.singleton Yield) (Atomic $ Prop "han")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "han", "call", "thr", "ret"]
        )
      , ( "Rejecting inner ChainBack Yield"
        , False
        , formulaAt 4 $ ChainBack (PS.singleton Yield) (Atomic $ Prop "call")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "call", "han", "ret", "ret"]
        )
      , ( "Accepting ChainBack Equal"
        , True
        , formulaAt 3 $ ChainBack (PS.singleton Equal) (Atomic $ Prop "call")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "han", "ret"]
        )
      , ( "Rejecting Not ChainBack Equal"
        , False
        , formulaAt 3 $ Not (ChainBack (PS.singleton Equal) (Atomic $ Prop "call"))
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "han", "ret"]
        )
      , ( "Rejecting ChainBack Equal"
        , False
        , formulaAt 3 $ ChainBack (PS.singleton Equal) (Atomic $ Prop "han")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["han", "thr", "ret"]
        )
      , ( "Accepting inner ChainBack Equal"
        , True
        , formulaAt 4 $ ChainBack (PS.singleton Equal) (Atomic $ Prop "call")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "call", "han", "ret", "ret"]
        )
      , ( "Rejecting inner ChainBack Equal"
        , False
        , formulaAt 4 $ ChainBack (PS.singleton Equal) (Atomic $ Prop "han")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "han", "thr", "ret", "ret"]
        )
      , ( "Accepting ChainBack Take"
        , True
        , formulaAt 3 $ ChainBack (PS.singleton Take) (Atomic $ Prop "han")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["han", "thr", "ret"]
        )
      , ( "Rejecting Not ChainBack Take"
        , False
        , formulaAt 3 $ Not (ChainBack (PS.singleton Take) (Atomic $ Prop "han"))
        , stlPrecRelV1
        , map (S.singleton . Prop) ["han", "thr", "ret"]
        )
      , ( "Rejecting ChainBack Take"
        , False
        , formulaAt 3 $ ChainBack (PS.singleton Take) (Atomic $ Prop "call")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "han", "ret"]
        )
      , ( "Accepting inner ChainBack Take"
        , True
        , formulaAt 4 $ ChainBack (PS.singleton Take) (Atomic $ Prop "han")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "han", "thr", "ret"]
        )
      , ( "Rejecting inner ChainBack Take"
        , False
        , formulaAt 4 $ ChainBack (PS.singleton Take) (Atomic $ Prop "call")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "call", "han", "thr", "ret", "ret"]
        )
      , ( "Accepting ChainBack Take through inner ChainBack Yield"
        , True
        , formulaAt 5 $ ChainBack (PS.singleton Take) (Atomic $ Prop "han")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["han", "call", "thr", "thr", "ret"]
        )
      , ( "Rejecting ChainBack Take with inner ChainBack Yield"
        , False
        , formulaAt 5 $ ChainBack (PS.singleton Take) (Atomic $ Prop "call")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["han", "call", "thr", "thr", "ret"]
        )
      , ( "Accepting ChainBack Take through union of Yield and Take checksets"
        , True
        , formulaAt 4 $ ChainBack (PS.singleton Take) (Atomic $ Prop "call")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "call", "call", "thr"]
        )
      , ( "Accepting ChainBack YE through ChainBack Yield"
        , True
        , formulaAt 3 $ ChainBack (PS.fromList [Yield, Equal]) (Atomic $ Prop "han")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["han", "call", "thr"]
        )
      , ( "Accepting ChainBack YT through ChainBack Yield"
        , True
        , formulaAt 3 $ ChainBack (PS.fromList [Yield, Take]) (Atomic $ Prop "han")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["han", "call", "thr"]
        )
      , ( "Accepting ChainBack YE through ChainBack Equal"
        , True
        , formulaAt 3 $ ChainBack (PS.fromList [Equal, Yield]) (Atomic $ Prop "call")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "han", "ret"]
        )
      , ( "Accepting ChainBack ET through ChainBack Equal"
        , True
        , formulaAt 3 $ ChainBack (PS.fromList [Equal, Take]) (Atomic $ Prop "call")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "han", "ret"]
        )
      , ( "Accepting ChainBack ET through ChainBack Take"
        , True
        , formulaAt 3 $ ChainBack (PS.fromList [Take, Equal]) (Atomic $ Prop "han")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["han", "thr", "ret"]
        )
      , ( "Accepting ChainBack YT through ChainBack Take"
        , True
        , formulaAt 3 $ ChainBack (PS.fromList [Take, Yield]) (Atomic $ Prop "han")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["han", "thr", "ret"]
        )
      , ( "Accepting ChainBack YET through ChainBack Yield"
        , True
        , formulaAt 3 $ ChainBack (PS.fromList [Yield, Equal, Take]) (Atomic $ Prop "han")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["han", "call", "thr"]
        )
      , ( "Accepting ChainBack YET through ChainBack Equal"
        , True
        , formulaAt 3 $ ChainBack (PS.fromList [Yield, Equal, Take]) (Atomic $ Prop "call")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "han", "ret"]
        )
      , ( "Accepting ChainBack YET through ChainBack Take"
        , True
        , formulaAt 3 $ ChainBack (PS.fromList [Yield, Equal, Take]) (Atomic $ Prop "han")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["han", "thr", "ret"]
        )
      , ( "Rejecting Not ChainBack YET through ChainBack Yield"
        , False
        , formulaAt 3 $ Not (ChainBack (PS.fromList [Yield, Equal, Take]) (Atomic $ Prop "han"))
        , stlPrecRelV1
        , map (S.singleton . Prop) ["han", "call", "thr"]
        )
      , ( "Rejecting Not ChainBack YET through ChainBack Equal"
        , False
        , formulaAt 3 $ Not (ChainBack (PS.fromList [Yield, Equal, Take]) (Atomic $ Prop "call"))
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "han", "ret"]
        )
      , ( "Rejecting Not ChainBack YET through ChainBack Take"
        , False
        , formulaAt 3 $ Not (ChainBack (PS.fromList [Yield, Equal, Take]) (Atomic $ Prop "han"))
        , stlPrecRelV1
        , map (S.singleton . Prop) ["han", "thr", "ret"]
        )
      , ( "Accepting Since Y through ChainBack Yield"
        , True
        , formulaAt 3 $ Since (PS.singleton Yield) (Not . Atomic . Prop $ "call") (Atomic . Prop $ "han")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["han", "call", "thr"]
        )
      , ( "Rejecting Since Y"
        , False
        , formulaAt 3 $ Since (PS.singleton Yield) (Not . Atomic . Prop $ "thr") (Atomic . Prop $ "han")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["han", "call", "thr"]
        )
      , ( "Accepting Since E through ChainBack Equal"
        , True
        , formulaAt 3 $ Since (PS.singleton Equal) (Not . Atomic . Prop $ "han") (Atomic . Prop $ "call")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "han", "ret"]
        )
      , ( "Rejecting Since E"
        , False
        , formulaAt 3 $ Since (PS.singleton Equal) (Not . Atomic . Prop $ "ret") (Atomic . Prop $ "call")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "han", "ret"]
        )
      , ( "Accepting Since T through ChainBack Take"
        , True
        , formulaAt 3 $ Since (PS.singleton Take) (Not . Atomic . Prop $ "thr") (Atomic . Prop $ "han")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["han", "thr", "ret"]
        )
      , ( "Rejecting Since T"
        , False
        , formulaAt 3 $ Since (PS.singleton Take) (Not . Atomic . Prop $ "ret") (Atomic . Prop $ "han")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["han", "thr", "ret"]
        )
      , ( "Accepting Since YET"
        , True
        , formulaAt 3 $ Since (PS.fromList [Yield, Equal, Take]) (Not . Atomic . Prop $ "call") (Atomic . Prop $ "call")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "han", "ret"]
        )
      , ( "Rejecting Not Since YET"
        , False
        , formulaAt 4 $ Not (Since (PS.fromList [Yield, Equal, Take]) (Not . Atomic . Prop $ "call") (Atomic . Prop $ "call"))
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "han", "ret"]
        )
      , ( "Rejecting Since YET"
        , False
        , formulaAt 3 $ Since (PS.fromList [Yield, Equal, Take]) (Not . Atomic . Prop $ "ret") (Atomic . Prop $ "call")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "han", "ret"]
        )
      , ( "Accepting HierNextYield"
        , True
        , formulaAt 3 $ HierNextYield (Atomic . Prop $ "thr")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["han", "call", "thr", "thr", "ret"]
        )
      , ( "Rejecting Not HierNextYield"
        , False
        , formulaAt 3 $ Not (HierNextYield (Atomic . Prop $ "thr"))
        , stlPrecRelV1
        , map (S.singleton . Prop) ["han", "call", "thr", "thr", "ret"]
        )
      , ( "Rejecting HierNextYield"
        , False
        , formulaAt 3 $ HierNextYield (Atomic . Prop $ "thr")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["han", "call", "thr", "ret"]
        )
      , ( "Accepting HierBackYield"
        , True
        , formulaAt 4 $ HierBackYield (Atomic . Prop $ "thr")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["han", "call", "thr", "thr", "ret"]
        )
      , ( "Rejecting Not HierBackYield"
        , False
        , formulaAt 4 $ Not (HierBackYield (Atomic . Prop $ "thr"))
        , stlPrecRelV1
        , map (S.singleton . Prop) ["han", "call", "thr", "thr", "ret"]
        )
      , ( "Rejecting HierBackYield"
        , False
        , formulaAt 3 $ HierBackYield (Atomic . Prop $ "call")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["han", "call", "thr", "ret"]
        )
      , ( "Accepting HierNextTake"
        , True
        , HierNextTake (Atomic . Prop $ "call")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "call", "call", "thr"]
        )
      , ( "Rejecting Not HierNextTake"
        , False
        , Not (HierNextTake (Atomic . Prop $ "call"))
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "call", "call", "thr"]
        )
      , ( "Rejecting HierNextTake"
        , False
        , formulaAt 2 $ HierNextTake (Atomic . Prop $ "call")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "call", "call", "thr"]
        )
      , ( "Accepting HierBackTake"
        , True
        , formulaAt 2 $ HierBackTake (Atomic . Prop $ "call")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "call", "call", "thr"]
        )
      , ( "Rejecting Not HierBackTake"
        , False
        , formulaAt 2 $ Not (HierBackTake (Atomic . Prop $ "call"))
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "call", "call", "thr"]
        )
      , ( "Rejecting HierBackTake"
        , False
        , formulaAt 3 $ HierBackTake (Atomic . Prop $ "call")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "call", "call", "thr"]
        )
      , ( "Accepting T"
        , True
        , T
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "han", "thr", "ret"]
        )
      , ( "Rejecting Not T"
        , False
        , Not T
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "han", "thr", "ret"]
        )
      , ( "Rejecting Not T"
        , False
        , Not T
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "han", "thr", "ret"]
        )
      , ( "Accepting HierUntilYield"
        , True
        , formulaAt 3 $ (Atomic . Prop $ "t") `HierUntilYield` (Atomic . Prop $ "tend")
        , stlPrecRelV1
        , map (S.fromList . map Prop) (stlAnnotateV1 ["han", "call", "t", "t", "t", "tend", "ret"])
        )
      , ( "Rejecting Not HierUntilYield"
        , False
        , formulaAt 3 $ Not ((Atomic . Prop $ "t") `HierUntilYield` (Atomic . Prop $ "tend"))
        , stlPrecRelV1
        , map (S.fromList . map Prop) (stlAnnotateV1 ["han", "call", "t", "t", "t", "tend", "ret"])
        )
      , ( "Rejecting HierUntilYield"
        , False
        , formulaAt 3 $ (Not . Atomic . Prop $ "texc") `HierUntilYield` (Atomic . Prop $ "tend")
        , stlPrecRelV1
        , map (S.fromList . map Prop) (stlAnnotateV1 ["han", "call", "t", "texc", "t", "tend", "ret"])
        )
      , ( "Accepting HierSinceYield"
        , True
        , formulaAt 6 $ (Atomic . Prop $ "t") `HierSinceYield` (Atomic . Prop $ "tbeg")
        , stlPrecRelV1
        , map (S.fromList . map Prop) (stlAnnotateV1 ["han", "call", "tbeg", "t", "t", "t", "ret"])
        )
      , ( "Rejecting Not HierSinceYield"
        , False
        , formulaAt 6 $ Not ((Atomic . Prop $ "t") `HierSinceYield` (Atomic . Prop $ "tbeg"))
        , stlPrecRelV1
        , map (S.fromList . map Prop) (stlAnnotateV1 ["han", "call", "tbeg", "t", "t", "t", "ret"])
        )
      , ( "Rejecting HierSinceYield"
        , False
        , formulaAt 6 $ (Not . Atomic . Prop $ "texc") `HierSinceYield` (Atomic . Prop $ "tbeg")
        , stlPrecRelV1
        , map (S.fromList . map Prop) (stlAnnotateV1 ["han", "call", "tbeg", "t", "texc", "t", "ret"])
        )
      , ( "Accepting HierUntilTake"
        , True
        , (Atomic . Prop $ "c") `HierUntilTake` (Atomic . Prop $ "cend")
        , stlPrecRelV1
        , map (S.fromList . map Prop) (stlAnnotateV1 ["c", "c", "cend", "call", "thr"])
        )
      , ( "Rejecting Not HierUntilTake"
        , False
        , Not ((Atomic . Prop $ "c") `HierUntilTake` (Atomic . Prop $ "cend"))
        , stlPrecRelV1
        , map (S.fromList . map Prop) (stlAnnotateV1 ["c", "c", "cend", "call", "thr"])
        )
      , ( "Rejecting HierUntilTake"
        , False
        , (Not . Atomic . Prop $ "cexc") `HierUntilTake` (Atomic . Prop $ "cend")
        , stlPrecRelV1
        , map (S.fromList . map Prop) (stlAnnotateV1 ["c", "cexc", "cend", "call", "thr"])
        )
      , ( "Accepting HierSinceTake"
        , True
        , formulaAt 3 $ (Atomic . Prop $ "c") `HierSinceTake` (Atomic . Prop $ "cbeg")
        , stlPrecRelV1
        , map (S.fromList . map Prop) (stlAnnotateV1 ["cbeg", "c", "c", "call", "thr"])
        )
      , ( "Rejecting Not HierSinceTake"
        , False
        , formulaAt 3 $ Not ((Atomic . Prop $ "c") `HierSinceTake` (Atomic . Prop $ "cbeg"))
        , stlPrecRelV1
        , map (S.fromList . map Prop) (stlAnnotateV1 ["cbeg", "c", "c", "call", "thr"])
        )
      , ( "Rejecting HierSinceTake"
        , False
        , formulaAt 3 $ (Not . Atomic . Prop $ "cexc") `HierSinceTake` (Atomic . Prop $ "cbeg")
        , stlPrecRelV1
        , map (S.fromList . map Prop) (stlAnnotateV1 ["cbeg", "cexc", "c", "call", "thr"])
        )
      , ( "Accepting Eventually'"
        , True
        , Eventually' (Atomic . Prop $ "thr")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "han", "thr", "ret"]
        )
      , ( "Rejecting Not Eventually'"
        , False
        , Not $ Eventually' (Atomic . Prop $ "thr")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "han", "thr", "ret"]
        )
      , ( "Rejecting Eventually'"
        , False
        , Eventually' (Atomic . Prop $ "thr")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "han", "ret"]
        )
      , ( "Testing boundaries with ChainNext"
        , True
        , ChainNext (PS.singleton Take) T
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "call"]
        )
      , ( "Testing boundaries with HierUntilTake"
        , True
        , HierUntilTake T (Atomic . Prop $ "call")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "call"]
        )
      ]

    potlv2Tests = testGroup "PotlV2, Stack Trace Lang V2" $ map makeTestCase
      [ ( "Accepting Xor"
        , True
        , (P2.Atomic . Prop $ "call") `P2.Xor` (P2.PNext P2.Down . P2.Atomic . Prop $ "exc")
        , stlPrecRelV2
        , map (S.singleton . Prop) ["call", "han", "exc", "ret"]
        )
      , ( "Rejecting Xor"
        , False
        , (P2.Atomic . Prop $ "call") `P2.Xor` (P2.PNext P2.Down . P2.Atomic . Prop $ "han")
        , stlPrecRelV2
        , map (S.singleton . Prop) ["call", "han", "exc", "ret"]
        )
      , ( "Accepting Implies" -- Ex falso quodlibet ;)
        , True
        , (P2.Atomic . Prop $ "ret") `P2.Implies` (P2.HNext P2.Up . P2.Atomic . Prop $ "han")
        , stlPrecRelV2
        , map (S.singleton . Prop) ["call", "han", "exc", "ret"]
        )
      , ( "Rejecting Implies"
        , False
        , (P2.Atomic . Prop $ "call") `P2.Implies` (P2.PNext P2.Down . P2.Atomic . Prop $ "ret")
        , stlPrecRelV2
        , map (S.singleton . Prop) ["call", "han", "exc", "ret"]
        )
      , ( "Accepting Iff"
        , True
        , (P2.Atomic . Prop $ "call") `P2.Iff` (P2.XNext P2.Up . P2.Atomic . Prop $ "ret")
        , stlPrecRelV2
        , map (S.singleton . Prop) ["call", "han", "exc", "ret"]
        )
      , ( "Rejecting Iff"
        , False
        , (P2.Atomic . Prop $ "call") `P2.Iff` (P2.XNext P2.Up . P2.Atomic . Prop $ "ret")
        , stlPrecRelV2
        , map (S.singleton . Prop) ["call", "han", "exc"]
        )
      , ( "Accepting Eventually"
        , True
        , P2.Eventually . P2.Atomic . Prop $ "ret"
        , stlPrecRelV2
        , map (S.singleton . Prop) ["call", "han", "exc", "ret"]
        )
      , ( "Rejecting Eventually"
        , False
        , P2.Eventually . P2.Atomic . Prop $ "ret"
        , stlPrecRelV2
        , map (S.singleton . Prop) ["call", "han", "exc"]
        )
      , ( "Accepting Always"
        , True
        , P2.Always . P2.Atomic . Prop $ "call"
        , stlPrecRelV2
        , map (S.singleton . Prop) ["call", "call", "call"]
        )
      , ( "Rejecting Always"
        , False
        , P2.Always . P2.Atomic . Prop $ "call"
        , stlPrecRelV2
        , map (S.singleton . Prop) ["call", "han", "call"]
        )
      , ( "Accepting HUntil Down"
        , True
        , P2.PNext P2.Down (P2.HUntil P2.Down P2.T (P2.Atomic . Prop $ "call"))
        , stlPrecRelV2
        , map (S.singleton . Prop) ["han", "call", "call", "call", "exc", "ret"]
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
            , P2.Always $ (P2.Atomic . Prop $ "call") `P2.Implies` ((P2.PNext P2.Down . P2.Atomic . Prop $ "ret") `P2.Or` (P2.XNext P2.Down . P2.Atomic . Prop $ "ret"))
            , stlPrecRelV1
            , \m -> map (S.singleton . Prop) <$> wellFormedTrace m
            )
          , ( "Well formed stack traces, all exceptions are handled"
            , True
            , P2.Always $ (P2.Atomic . Prop $ "thr") `P2.Implies` ((P2.PBack P2.Down . P2.Atomic . Prop $ "han") `P2.Or` (P2.XBack P2.Down . P2.Atomic . Prop $ "han"))
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

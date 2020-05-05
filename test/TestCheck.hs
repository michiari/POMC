module TestCheck ( tests
                 , termTrace) where

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck

import qualified Data.Set as S

import Control.Monad

import POMC.Check (check)
import POMC.Example (stlPrecedence, stlAnnotate)
import POMC.Opa (Prec(..))
import POMC.Potl (Formula(..), Prop(..), formulaAt)

-- Each unit test is a tuple of the type:
-- (name, expected check result, phi, prec, input)
unitTuples =
  [ ( "Stack trace lang, accepting predicate on first word position"
    , True
    , Atomic . Prop  $ "call"
    , stlPrecedence
    , map (S.singleton . Prop) ["call", "ret"]
    )
  , ( "Stack trace lang, rejecting Not predicate on first word position"
    , False
    , Not (Atomic . Prop  $ "call")
    , stlPrecedence
    , map (S.singleton . Prop) ["call", "ret"]
    )
  , ( "Stack trace lang, accepting Not"
    , True
    , Not . Atomic . Prop  $ "ret"
    , stlPrecedence
    , map (S.singleton . Prop) ["call", "ret"]
    )
  , ( "Stack trace lang, rejecting Not Not"
    , False
    , Not . Not . Atomic . Prop  $ "ret"
    , stlPrecedence
    , map (S.singleton . Prop) ["call", "ret"]
    )
  , ( "Stack trace lang, rejecting Not"
    , False
    , Not . Atomic . Prop  $ "call"
    , stlPrecedence
    , map (S.singleton . Prop) ["call", "ret"]
    )
  , ( "Stack trace lang, accepting multiple negation"
    , True
    , Not . Not . Not . Not . Atomic . Prop  $ "call"
    , stlPrecedence
    , map (S.singleton . Prop) ["call", "ret"]
    )
  , ( "Stack trace lang, rejecting multiple negation"
    , False
    , Not . Not . Not . Not . Not . Atomic . Prop  $ "call"
    , stlPrecedence
    , map (S.singleton . Prop) ["call", "ret"]
    )
  , ( "Stack trace lang, accepting And"
    , True
    , And (Atomic $ Prop "call") (Not $ Atomic $ Prop "ret")
    , stlPrecedence
    , map (S.singleton . Prop) ["call", "ret"]
    )
  , ( "Stack trace lang, rejecting Not And"
    , False
    , Not (And (Atomic $ Prop "call") (Not $ Atomic $ Prop "ret"))
    , stlPrecedence
    , map (S.singleton . Prop) ["call", "ret"]
    )
  , ( "Stack trace lang, accepting Or"
    , True
    , Or (Atomic . Prop $ "call") (Atomic . Prop $ "ret")
    , stlPrecedence
    , map (S.singleton . Prop) ["call", "ret"]
    )
  , ( "Stack trace lang, rejecting Not Or"
    , False
    , Not (Or (Atomic . Prop $ "call") (Atomic . Prop $ "ret"))
    , stlPrecedence
    , map (S.singleton . Prop) ["call", "ret"]
    )
  , ( "Stack trace lang, accepting PrecNext"
    , True
    , PrecNext (S.singleton Equal) (Atomic $ Prop "ret")
    , stlPrecedence
    , map (S.singleton . Prop) ["call", "ret"]
    )
  , ( "Stack trace lang, rejecting Not PrecNext"
    , False
    , Not $ PrecNext (S.singleton Equal) (Atomic $ Prop "ret")
    , stlPrecedence
    , map (S.singleton . Prop) ["call", "ret"]
    )
  , ( "Stack trace lang, rejecting PrecNext"
    , False
    , PrecNext (S.singleton Equal) (Atomic $ Prop "call")
    , stlPrecedence
    , map (S.singleton . Prop) ["call", "ret"]
    )
  , ( "Stack trace lang, rejecting OOB PrecNext"
    , False
    , PrecNext (S.singleton Equal) (PrecNext (S.singleton Take) (Atomic $ Prop "call"))
    , stlPrecedence
    , map (S.singleton . Prop) ["call", "ret"]
    )
  , ( "Stack trace lang, accepting PrecBack"
    , True
    , PrecNext (S.singleton Equal) (PrecBack (S.singleton Equal) (Atomic $ Prop "call"))
    , stlPrecedence
    , map (S.singleton . Prop) ["call", "ret"]
    )
  , ( "Stack trace lang, rejecting Not PrecBack"
    , False
    , PrecNext (S.singleton Equal) $ Not (PrecBack (S.singleton Equal) (Atomic $ Prop "call"))
    , stlPrecedence
    , map (S.singleton . Prop) ["call", "ret"]
    )
  , ( "Stack trace lang, rejecting PrecBack"
    , False
    , PrecNext (S.singleton Equal) (PrecBack (S.fromList [Yield, Take]) (Atomic $ Prop "call"))
    , stlPrecedence
    , map (S.singleton . Prop) ["call", "ret"]
    )
  , ( "Stack trace lang, rejecting OOB PrecBack"
    , False
    , PrecBack (S.fromList [Yield, Equal, Take]) (Atomic $ Prop "call")
    , stlPrecedence
    , map (S.singleton . Prop) ["call", "ret"]
    )
  , ( "Stack trace lang, rejecting OOB PrecBack"
    , False
    , PrecBack (S.fromList [Yield, Equal, Take]) $ PrecBack (S.fromList [Yield, Equal, Take]) (Atomic $ Prop "call")
    , stlPrecedence
    , map (S.singleton . Prop) ["call", "ret"]
    )
  , ( "Stack trace lang, accepting ChainNext Yield"
    , True
    , ChainNext (S.singleton Yield) (Atomic $ Prop "thr")
    , stlPrecedence
    , map (S.singleton . Prop) ["han", "call", "thr"]
    )
  , ( "Stack trace lang, rejecting Not ChainNext Yield"
    , False
    , Not $ ChainNext (S.singleton Yield) (Atomic $ Prop "thr")
    , stlPrecedence
    , map (S.singleton . Prop) ["han", "call", "thr"]
    )
  , ( "Stack trace lang, rejecting ChainNext Yield"
    , False
    , ChainNext (S.singleton Yield) (Atomic $ Prop "ret")
    , stlPrecedence
    , map (S.singleton . Prop) ["call", "han", "ret"]
    )
  , ( "Stack trace lang, accepting inner ChainNext Yield"
    , True
    , PrecNext (S.fromList [Yield, Equal, Take]) $ ChainNext (S.singleton Yield) (Atomic $ Prop "thr")
    , stlPrecedence
    , map (S.singleton . Prop) ["call", "han", "call", "thr", "ret"]
    )
  , ( "Stack trace lang, rejecting inner ChainNext Yield"
    , False
    , PrecNext (S.fromList [Yield, Equal, Take]) $ ChainNext (S.singleton Yield) (Atomic $ Prop "ret")
    , stlPrecedence
    , map (S.singleton . Prop) ["call", "han", "call", "thr", "ret"]
    )
  , ( "Stack trace lang, push after pop with ChainNext Yield in closure"
    , True
    , Or (ChainNext (S.singleton Yield) (Atomic $ Prop "call")) (Atomic $ Prop "call")
    , stlPrecedence
    , map (S.singleton . Prop) ["call", "ret", "call", "ret"]
    )
  , ( "Stack trace lang, accepting ChainNext Equal"
    , True
    , ChainNext (S.singleton Equal) (Atomic $ Prop "ret")
    , stlPrecedence
    , map (S.singleton . Prop) ["call", "han", "ret"]
    )
  , ( "Stack trace lang, rejecting Not ChainNext Equal"
    , False
    , Not $ ChainNext (S.singleton Equal) (Atomic $ Prop "ret")
    , stlPrecedence
    , map (S.singleton . Prop) ["call", "han", "ret"]
    )
  , ( "Stack trace lang, rejecting ChainNext Equal"
    , False
    , ChainNext (S.singleton Equal) (Atomic $ Prop "ret")
    , stlPrecedence
    , map (S.singleton . Prop) ["han", "thr", "ret"]
    )
  , ( "Stack trace lang, accepting inner ChainNext Equal"
    , True
    , PrecNext (S.fromList [Yield, Equal, Take]) $ ChainNext (S.singleton Equal) (Atomic $ Prop "ret")
    , stlPrecedence
    , map (S.singleton . Prop) ["call", "call", "han", "ret", "ret"]
    )
  , ( "Stack trace lang, rejecting inner ChainNext Equal"
    , False
    , PrecNext (S.fromList [Yield, Equal, Take]) $ ChainNext (S.singleton Equal) (Atomic $ Prop "ret")
    , stlPrecedence
    , map (S.singleton . Prop) ["call", "han", "thr", "ret", "ret"]
    )
  , ( "Stack trace lang, accepting ChainNext Take"
    , True
    , ChainNext (S.singleton Take) (Atomic $ Prop "ret")
    , stlPrecedence
    , map (S.singleton . Prop) ["han", "thr", "ret"]
    )
  , ( "Stack trace lang, rejecting Not ChainNext Take"
    , False
    , Not $ ChainNext (S.singleton Take) (Atomic $ Prop "ret")
    , stlPrecedence
    , map (S.singleton . Prop) ["han", "thr", "ret"]
    )
  , ( "Stack trace lang, rejecting ChainNext Take"
    , False
    , ChainNext (S.singleton Take) (Atomic $ Prop "ret")
    , stlPrecedence
    , map (S.singleton . Prop) ["call", "han", "ret"]
    )
  , ( "Stack trace lang, accepting inner ChainNext Take"
    , True
    , PrecNext (S.fromList [Yield, Equal, Take]) $ ChainNext (S.singleton Take) (Atomic $ Prop "ret")
    , stlPrecedence
    , map (S.singleton . Prop) ["call", "han", "thr", "ret"]
    )
  , ( "Stack trace lang, rejecting inner ChainNext Take"
    , False
    , PrecNext (S.fromList [Yield, Equal, Take]) $ ChainNext (S.singleton Take) (Atomic $ Prop "ret")
    , stlPrecedence
    , map (S.singleton . Prop) ["call", "call", "han", "thr", "ret", "ret"]
    )
  , ( "Stack trace lang, accepting ChainNext YET through ChainNext Equal"
    , True
    , ChainNext (S.fromList [Yield, Equal, Take]) (Atomic $ Prop "ret")
    , stlPrecedence
    , map (S.singleton . Prop) ["call", "han", "ret"]
    )
  , ( "Stack trace lang, accepting ChainNext YET through ChainNext Yield"
    , True
    , ChainNext (S.fromList [Yield, Equal, Take]) (Atomic $ Prop "thr")
    , stlPrecedence
    , map (S.singleton . Prop) ["han", "call", "thr"]
    )
  , ( "Stack trace lang, accepting ChainNext YET through ChainNext Take"
    , True
    , ChainNext (S.fromList [Yield, Equal, Take]) (Atomic $ Prop "ret")
    , stlPrecedence
    , map (S.singleton . Prop) ["han", "thr", "ret"]
    )
  , ( "Stack trace lang, rejecting Not ChainNext YET through ChainNext Equal"
    , False
    , Not $ ChainNext (S.fromList [Yield, Equal, Take]) (Atomic $ Prop "ret")
    , stlPrecedence
    , map (S.singleton . Prop) ["call", "han", "ret"]
    )
  , ( "Stack trace lang, rejecting Not ChainNext YET through ChainNext Yield"
    , False
    , Not $ ChainNext (S.fromList [Yield, Equal, Take]) (Atomic $ Prop "thr")
    , stlPrecedence
    , map (S.singleton . Prop) ["han", "call", "thr"]
    )
  , ( "Stack trace lang, rejecting Not ChainNext YET through ChainNext Take"
    , False
    , Not $ ChainNext (S.fromList [Yield, Equal, Take]) (Atomic $ Prop "ret")
    , stlPrecedence
    , map (S.singleton . Prop) ["han", "thr", "ret"]
    )
  , ( "Stack trace lang, rejecting Not Or of ChainNext forumulas through ChainNext Take"
    , False
    , Not $ (Or (ChainNext (S.singleton Yield) (Atomic $ Prop "ret")) (Or (ChainNext (S.singleton Equal) (Atomic $ Prop "ret")) (ChainNext (S.singleton Take) (Atomic $ Prop "ret"))))
    , stlPrecedence
    , map (S.singleton . Prop) ["han", "thr", "ret"]
    )
  , ( "Stack trace lang, rejecting ChainNext YET"
    , False
    , ChainNext (S.fromList [Yield, Equal, Take]) (Atomic $ Prop "ret")
    , stlPrecedence
    , map (S.singleton . Prop) ["call", "ret"] -- there is no inner chain ;)
    )
  , ( "Stack trace lang, rejecting ChainNext YT"
    , False
    , ChainNext (S.fromList [Yield, Take]) (Atomic $ Prop "ret")
    , stlPrecedence
    , map (S.singleton . Prop) ["call", "han", "ret"]
    )
  , ( "Stack trace lang, rejecting ChainNext ET"
    , False
    , ChainNext (S.fromList [Equal, Take]) (Atomic $ Prop "ret")
    , stlPrecedence
    , map (S.singleton . Prop) ["han", "call", "thr"]
    )
  , ( "Stack trace lang, rejecting ChainNext YE"
    , False
    , ChainNext (S.fromList [Yield, Equal]) (Atomic $ Prop "ret")
    , stlPrecedence
    , map (S.singleton . Prop) ["han", "thr", "ret"]
    )
  , ( "Stack trace lang, accepting Until Y through ChainNext Yield"
    , True
    , Until (S.singleton Yield) (Not . Atomic . Prop $ "call") (Atomic $ Prop "thr")
    , stlPrecedence
    , map (S.singleton . Prop) ["han", "call", "thr"]
    )
  , ( "Stack trace lang, rejecting Until Y"
    , False
    , Until (S.singleton Yield) (Not . Atomic . Prop $ "han") (Atomic $ Prop "thr")
    , stlPrecedence
    , map (S.singleton . Prop) ["han", "call", "thr"]
    )
  , ( "Stack trace lang, accepting Until E through ChainNext Equal"
    , True
    , Until (S.singleton Equal) (Not . Atomic . Prop $ "han") (Atomic $ Prop "ret")
    , stlPrecedence
    , map (S.singleton . Prop) ["call", "han", "ret"]
    )
  , ( "Stack trace lang, rejecting Until E"
    , False
    , Until (S.singleton Equal) (Not . Atomic . Prop $ "call") (Atomic $ Prop "ret")
    , stlPrecedence
    , map (S.singleton . Prop) ["call", "han", "ret"]
    )
  , ( "Stack trace lang, accepting Until T through ChainNext Take"
    , True
    , Until (S.singleton Take) (Not . Atomic . Prop $ "thr") (Atomic $ Prop "ret")
    , stlPrecedence
    , map (S.singleton . Prop) ["han", "thr", "ret"]
    )
  , ( "Stack trace lang, rejecting Until T"
    , False
    , Until (S.singleton Take) (Not . Atomic . Prop $ "han") (Atomic $ Prop "ret")
    , stlPrecedence
    , map (S.singleton . Prop) ["han", "thr", "ret"]
    )
  , ( "Stack trace lang, accepting Until YET"
    , True
    , Until (S.fromList [Yield, Equal, Take]) (Not . Atomic . Prop $ "ret") (Atomic $ Prop "han")
    , stlPrecedence
    , map (S.singleton . Prop) ["call", "han", "thr", "ret"]
    )
  , ( "Stack trace lang, rejecting Not Until YET"
    , False
    , Not (Until (S.fromList [Yield, Equal, Take]) (Not . Atomic . Prop $ "ret") (Atomic $ Prop "han"))
    , stlPrecedence
    , map (S.singleton . Prop) ["call", "han", "thr", "ret"]
    )
  , ( "Stack trace lang, accepting Until YET" -- this fails if the Until conditions for an atom
    , True                                    -- are implemented with XOR instead of OR
    , Until (S.fromList [Yield, Equal, Take]) (Not . Atomic . Prop $ "thr") (Atomic $ Prop "ret")
    , stlPrecedence
    , map (S.singleton . Prop) ["call", "han", "thr", "ret"]
    )
  , ( "Stack trace lang, rejecting Not Until YET"
    , False
    , Not (Until (S.fromList [Yield, Equal, Take]) (Not . Atomic . Prop $ "thr") (Atomic $ Prop "ret"))
    , stlPrecedence
    , map (S.singleton . Prop) ["call", "han", "thr", "ret"]
    )
  , ( "Stack trace lang, accepting ChainBack Yield"
    , True
    , formulaAt 3 $ ChainBack (S.singleton Yield) (Atomic $ Prop "han")
    , stlPrecedence
    , map (S.singleton . Prop) ["han", "call", "thr"]
    )
  , ( "Stack trace lang, rejecting Not ChainBack Yield"
    , False
    , formulaAt 3 $ Not (ChainBack (S.singleton Yield) (Atomic $ Prop "han"))
    , stlPrecedence
    , map (S.singleton . Prop) ["han", "call", "thr"]
    )
  , ( "Stack trace lang, rejecting ChainBack Yield"
    , False
    , formulaAt 3 $ ChainBack (S.singleton Yield) (Atomic $ Prop "call")
    , stlPrecedence
    , map (S.singleton . Prop) ["call", "han", "ret"]
    )
  , ( "Stack trace lang, accepting inner ChainBack Yield"
    , True
    , formulaAt 4 $ ChainBack (S.singleton Yield) (Atomic $ Prop "han")
    , stlPrecedence
    , map (S.singleton . Prop) ["call", "han", "call", "thr", "ret"]
    )
  , ( "Stack trace lang, rejecting inner ChainBack Yield"
    , False
    , formulaAt 4 $ ChainBack (S.singleton Yield) (Atomic $ Prop "call")
    , stlPrecedence
    , map (S.singleton . Prop) ["call", "call", "han", "ret", "ret"]
    )
  , ( "Stack trace lang, accepting ChainBack Equal"
    , True
    , formulaAt 3 $ ChainBack (S.singleton Equal) (Atomic $ Prop "call")
    , stlPrecedence
    , map (S.singleton . Prop) ["call", "han", "ret"]
    )
  , ( "Stack trace lang, rejecting Not ChainBack Equal"
    , False
    , formulaAt 3 $ Not (ChainBack (S.singleton Equal) (Atomic $ Prop "call"))
    , stlPrecedence
    , map (S.singleton . Prop) ["call", "han", "ret"]
    )
  , ( "Stack trace lang, rejecting ChainBack Equal"
    , False
    , formulaAt 3 $ ChainBack (S.singleton Equal) (Atomic $ Prop "han")
    , stlPrecedence
    , map (S.singleton . Prop) ["han", "thr", "ret"]
    )
  , ( "Stack trace lang, accepting inner ChainBack Equal"
    , True
    , formulaAt 4 $ ChainBack (S.singleton Equal) (Atomic $ Prop "call")
    , stlPrecedence
    , map (S.singleton . Prop) ["call", "call", "han", "ret", "ret"]
    )
  , ( "Stack trace lang, rejecting inner ChainBack Equal"
    , False
    , formulaAt 4 $ ChainBack (S.singleton Equal) (Atomic $ Prop "han")
    , stlPrecedence
    , map (S.singleton . Prop) ["call", "han", "thr", "ret", "ret"]
    )
  , ( "Stack trace lang, accepting ChainBack Take"
    , True
    , formulaAt 3 $ ChainBack (S.singleton Take) (Atomic $ Prop "han")
    , stlPrecedence
    , map (S.singleton . Prop) ["han", "thr", "ret"]
    )
  , ( "Stack trace lang, rejecting Not ChainBack Take"
    , False
    , formulaAt 3 $ Not (ChainBack (S.singleton Take) (Atomic $ Prop "han"))
    , stlPrecedence
    , map (S.singleton . Prop) ["han", "thr", "ret"]
    )
  , ( "Stack trace lang, rejecting ChainBack Take"
    , False
    , formulaAt 3 $ ChainBack (S.singleton Take) (Atomic $ Prop "call")
    , stlPrecedence
    , map (S.singleton . Prop) ["call", "han", "ret"]
    )
  , ( "Stack trace lang, accepting inner ChainBack Take"
    , True
    , formulaAt 4 $ ChainBack (S.singleton Take) (Atomic $ Prop "han")
    , stlPrecedence
    , map (S.singleton . Prop) ["call", "han", "thr", "ret"]
    )
  , ( "Stack trace lang, rejecting inner ChainBack Take"
    , False
    , formulaAt 4 $ ChainBack (S.singleton Take) (Atomic $ Prop "call")
    , stlPrecedence
    , map (S.singleton . Prop) ["call", "call", "han", "thr", "ret", "ret"]
    )
  , ( "Stack trace lang, accepting ChainBack Take through inner ChainBack Yield"
    , True
    , formulaAt 5 $ ChainBack (S.singleton Take) (Atomic $ Prop "han")
    , stlPrecedence
    , map (S.singleton . Prop) ["han", "call", "thr", "thr", "ret"]
    )
  , ( "Stack trace lang, rejecting ChainBack Take with inner ChainBack Yield"
    , False
    , formulaAt 5 $ ChainBack (S.singleton Take) (Atomic $ Prop "call")
    , stlPrecedence
    , map (S.singleton . Prop) ["han", "call", "thr", "thr", "ret"]
    )
  , ( "Stack trace lang, accepting ChainBack Take through union of Yield and Take checksets"
    , True
    , formulaAt 4 $ ChainBack (S.singleton Take) (Atomic $ Prop "call")
    , stlPrecedence
    , map (S.singleton . Prop) ["call", "call", "call", "thr"]
    )
  , ( "Stack trace lang, accepting ChainBack YE through ChainBack Yield"
    , True
    , formulaAt 3 $ ChainBack (S.fromList [Yield, Equal]) (Atomic $ Prop "han")
    , stlPrecedence
    , map (S.singleton . Prop) ["han", "call", "thr"]
    )
  , ( "Stack trace lang, accepting ChainBack YT through ChainBack Yield"
    , True
    , formulaAt 3 $ ChainBack (S.fromList [Yield, Take]) (Atomic $ Prop "han")
    , stlPrecedence
    , map (S.singleton . Prop) ["han", "call", "thr"]
    )
  , ( "Stack trace lang, accepting ChainBack YE through ChainBack Equal"
    , True
    , formulaAt 3 $ ChainBack (S.fromList [Equal, Yield]) (Atomic $ Prop "call")
    , stlPrecedence
    , map (S.singleton . Prop) ["call", "han", "ret"]
    )
  , ( "Stack trace lang, accepting ChainBack ET through ChainBack Equal"
    , True
    , formulaAt 3 $ ChainBack (S.fromList [Equal, Take]) (Atomic $ Prop "call")
    , stlPrecedence
    , map (S.singleton . Prop) ["call", "han", "ret"]
    )
  , ( "Stack trace lang, accepting ChainBack ET through ChainBack Take"
    , True
    , formulaAt 3 $ ChainBack (S.fromList [Take, Equal]) (Atomic $ Prop "han")
    , stlPrecedence
    , map (S.singleton . Prop) ["han", "thr", "ret"]
    )
  , ( "Stack trace lang, accepting ChainBack YT through ChainBack Take"
    , True
    , formulaAt 3 $ ChainBack (S.fromList [Take, Yield]) (Atomic $ Prop "han")
    , stlPrecedence
    , map (S.singleton . Prop) ["han", "thr", "ret"]
    )
  , ( "Stack trace lang, accepting ChainBack YET through ChainBack Yield"
    , True
    , formulaAt 3 $ ChainBack (S.fromList [Yield, Equal, Take]) (Atomic $ Prop "han")
    , stlPrecedence
    , map (S.singleton . Prop) ["han", "call", "thr"]
    )
  , ( "Stack trace lang, accepting ChainBack YET through ChainBack Equal"
    , True
    , formulaAt 3 $ ChainBack (S.fromList [Yield, Equal, Take]) (Atomic $ Prop "call")
    , stlPrecedence
    , map (S.singleton . Prop) ["call", "han", "ret"]
    )
  , ( "Stack trace lang, accepting ChainBack YET through ChainBack Take"
    , True
    , formulaAt 3 $ ChainBack (S.fromList [Yield, Equal, Take]) (Atomic $ Prop "han")
    , stlPrecedence
    , map (S.singleton . Prop) ["han", "thr", "ret"]
    )
  , ( "Stack trace lang, rejecting Not ChainBack YET through ChainBack Yield"
    , False
    , formulaAt 3 $ Not (ChainBack (S.fromList [Yield, Equal, Take]) (Atomic $ Prop "han"))
    , stlPrecedence
    , map (S.singleton . Prop) ["han", "call", "thr"]
    )
  , ( "Stack trace lang, rejecting Not ChainBack YET through ChainBack Equal"
    , False
    , formulaAt 3 $ Not (ChainBack (S.fromList [Yield, Equal, Take]) (Atomic $ Prop "call"))
    , stlPrecedence
    , map (S.singleton . Prop) ["call", "han", "ret"]
    )
  , ( "Stack trace lang, rejecting Not ChainBack YET through ChainBack Take"
    , False
    , formulaAt 3 $ Not (ChainBack (S.fromList [Yield, Equal, Take]) (Atomic $ Prop "han"))
    , stlPrecedence
    , map (S.singleton . Prop) ["han", "thr", "ret"]
    )
  , ( "Stack trace lang, accepting Since Y through ChainBack Yield"
    , True
    , formulaAt 3 $ Since (S.singleton Yield) (Not . Atomic . Prop $ "call") (Atomic . Prop $ "han")
    , stlPrecedence
    , map (S.singleton . Prop) ["han", "call", "thr"]
    )
  , ( "Stack trace lang, rejecting Since Y"
    , False
    , formulaAt 3 $ Since (S.singleton Yield) (Not . Atomic . Prop $ "thr") (Atomic . Prop $ "han")
    , stlPrecedence
    , map (S.singleton . Prop) ["han", "call", "thr"]
    )
  , ( "Stack trace lang, accepting Since E through ChainBack Equal"
    , True
    , formulaAt 3 $ Since (S.singleton Equal) (Not . Atomic . Prop $ "han") (Atomic . Prop $ "call")
    , stlPrecedence
    , map (S.singleton . Prop) ["call", "han", "ret"]
    )
  , ( "Stack trace lang, rejecting Since E"
    , False
    , formulaAt 3 $ Since (S.singleton Equal) (Not . Atomic . Prop $ "ret") (Atomic . Prop $ "call")
    , stlPrecedence
    , map (S.singleton . Prop) ["call", "han", "ret"]
    )
  , ( "Stack trace lang, accepting Since T through ChainBack Take"
    , True
    , formulaAt 3 $ Since (S.singleton Take) (Not . Atomic . Prop $ "thr") (Atomic . Prop $ "han")
    , stlPrecedence
    , map (S.singleton . Prop) ["han", "thr", "ret"]
    )
  , ( "Stack trace lang, rejecting Since T"
    , False
    , formulaAt 3 $ Since (S.singleton Take) (Not . Atomic . Prop $ "ret") (Atomic . Prop $ "han")
    , stlPrecedence
    , map (S.singleton . Prop) ["han", "thr", "ret"]
    )
  , ( "Stack trace lang, accepting Since YET"
    , True
    , formulaAt 3 $ Since (S.fromList [Yield, Equal, Take]) (Not . Atomic . Prop $ "call") (Atomic . Prop $ "call")
    , stlPrecedence
    , map (S.singleton . Prop) ["call", "han", "ret"]
    )
  , ( "Stack trace lang, rejecting Not Since YET"
    , False
    , formulaAt 4 $ Not (Since (S.fromList [Yield, Equal, Take]) (Not . Atomic . Prop $ "call") (Atomic . Prop $ "call"))
    , stlPrecedence
    , map (S.singleton . Prop) ["call", "han", "ret"]
    )
  , ( "Stack trace lang, rejecting Since YET"
    , False
    , formulaAt 3 $ Since (S.fromList [Yield, Equal, Take]) (Not . Atomic . Prop $ "ret") (Atomic . Prop $ "call")
    , stlPrecedence
    , map (S.singleton . Prop) ["call", "han", "ret"]
    )
  , ( "Stack trace lang, accepting HierNextYield"
    , True
    , formulaAt 3 $ HierNextYield (Atomic . Prop $ "thr")
    , stlPrecedence
    , map (S.singleton . Prop) ["han", "call", "thr", "thr", "ret"]
    )
  , ( "Stack trace lang, rejecting Not HierNextYield"
    , False
    , formulaAt 3 $ Not (HierNextYield (Atomic . Prop $ "thr"))
    , stlPrecedence
    , map (S.singleton . Prop) ["han", "call", "thr", "thr", "ret"]
    )
  , ( "Stack trace lang, rejecting HierNextYield"
    , False
    , formulaAt 3 $ HierNextYield (Atomic . Prop $ "thr")
    , stlPrecedence
    , map (S.singleton . Prop) ["han", "call", "thr", "ret"]
    )
  , ( "Stack trace lang, accepting HierBackYield"
    , True
    , formulaAt 4 $ HierBackYield (Atomic . Prop $ "thr")
    , stlPrecedence
    , map (S.singleton . Prop) ["han", "call", "thr", "thr", "ret"]
    )
  , ( "Stack trace lang, rejecting Not HierBackYield"
    , False
    , formulaAt 4 $ Not (HierBackYield (Atomic . Prop $ "thr"))
    , stlPrecedence
    , map (S.singleton . Prop) ["han", "call", "thr", "thr", "ret"]
    )
  , ( "Stack trace lang, rejecting HierBackYield"
    , False
    , formulaAt 3 $ HierBackYield (Atomic . Prop $ "call")
    , stlPrecedence
    , map (S.singleton . Prop) ["han", "call", "thr", "ret"]
    )
  , ( "Stack trace lang, accepting HierNextTake"
    , True
    , HierNextTake (Atomic . Prop $ "call")
    , stlPrecedence
    , map (S.singleton . Prop) ["call", "call", "call", "thr"]
    )
  , ( "Stack trace lang, rejecting Not HierNextTake"
    , False
    , Not (HierNextTake (Atomic . Prop $ "call"))
    , stlPrecedence
    , map (S.singleton . Prop) ["call", "call", "call", "thr"]
    )
  , ( "Stack trace lang, rejecting HierNextTake"
    , False
    , formulaAt 2 $ HierNextTake (Atomic . Prop $ "call")
    , stlPrecedence
    , map (S.singleton . Prop) ["call", "call", "call", "thr"]
    )
  , ( "Stack trace lang, accepting HierBackTake"
    , True
    , formulaAt 2 $ HierBackTake (Atomic . Prop $ "call")
    , stlPrecedence
    , map (S.singleton . Prop) ["call", "call", "call", "thr"]
    )
  , ( "Stack trace lang, rejecting Not HierBackTake"
    , False
    , formulaAt 2 $ Not (HierBackTake (Atomic . Prop $ "call"))
    , stlPrecedence
    , map (S.singleton . Prop) ["call", "call", "call", "thr"]
    )
  , ( "Stack trace lang, rejecting HierBackTake"
    , False
    , formulaAt 3 $ HierBackTake (Atomic . Prop $ "call")
    , stlPrecedence
    , map (S.singleton . Prop) ["call", "call", "call", "thr"]
    )
  , ( "Stack trace lang, accepting T"
    , True
    , T
    , stlPrecedence
    , map (S.singleton . Prop) ["call", "han", "thr", "ret"]
    )
  , ( "Stack trace lang, rejecting Not T"
    , False
    , Not T
    , stlPrecedence
    , map (S.singleton . Prop) ["call", "han", "thr", "ret"]
    )
  , ( "Stack trace lang, rejecting Not T"
    , False
    , Not T
    , stlPrecedence
    , map (S.singleton . Prop) ["call", "han", "thr", "ret"]
    )
  , ( "Stack trace lang, accepting HierUntilYield"
    , True
    , formulaAt 3 $ (Atomic . Prop $ "t") `HierUntilYield` (Atomic . Prop $ "tend")
    , stlPrecedence
    , map (S.singleton . Prop) ["han", "call", "t", "t", "t", "tend", "ret"]
    )
  , ( "Stack trace lang, rejecting Not HierUntilYield"
    , False
    , formulaAt 3 $ Not ((Atomic . Prop $ "t") `HierUntilYield` (Atomic . Prop $ "tend"))
    , stlPrecedence
    , map (S.singleton . Prop) ["han", "call", "t", "t", "t", "tend", "ret"]
    )
  , ( "Stack trace lang, rejecting HierUntilYield"
    , False
    , formulaAt 3 $ (Not . Atomic . Prop $ "texc") `HierUntilYield` (Atomic . Prop $ "tend")
    , stlPrecedence
    , map (S.singleton . Prop) ["han", "call", "t", "texc", "t", "tend", "ret"]
    )
  , ( "Stack trace lang, accepting HierSinceYield"
    , True
    , formulaAt 6 $ (Atomic . Prop $ "t") `HierSinceYield` (Atomic . Prop $ "tbeg")
    , stlPrecedence
    , map (S.singleton . Prop) ["han", "call", "tbeg", "t", "t", "t", "ret"]
    )
  , ( "Stack trace lang, rejecting Not HierSinceYield"
    , False
    , formulaAt 6 $ Not ((Atomic . Prop $ "t") `HierSinceYield` (Atomic . Prop $ "tbeg"))
    , stlPrecedence
    , map (S.singleton . Prop) ["han", "call", "tbeg", "t", "t", "t", "ret"]
    )
  , ( "Stack trace lang, rejecting HierSinceYield"
    , False
    , formulaAt 6 $ (Not . Atomic . Prop $ "texc") `HierSinceYield` (Atomic . Prop $ "tbeg")
    , stlPrecedence
    , map (S.singleton . Prop) ["han", "call", "tbeg", "t", "texc", "t", "ret"]
    )
  , ( "Stack trace lang, accepting HierUntilTake"
    , True
    , (Atomic . Prop $ "c") `HierUntilTake` (Atomic . Prop $ "cend")
    , stlPrecedence
    , map (S.singleton . Prop) ["c", "c", "cend", "call", "thr"]
    )
  , ( "Stack trace lang, rejecting Not HierUntilTake"
    , False
    , Not ((Atomic . Prop $ "c") `HierUntilTake` (Atomic . Prop $ "cend"))
    , stlPrecedence
    , map (S.singleton . Prop) ["c", "c", "cend", "call", "thr"]
    )
  , ( "Stack trace lang, rejecting HierUntilTake"
    , False
    , (Not . Atomic . Prop $ "cexc") `HierUntilTake` (Atomic . Prop $ "cend")
    , stlPrecedence
    , map (S.singleton . Prop) ["c", "cexc", "cend", "call", "thr"]
    )
  , ( "Stack trace lang, accepting HierSinceTake"
    , True
    , formulaAt 3 $ (Atomic . Prop $ "c") `HierSinceTake` (Atomic . Prop $ "cbeg")
    , stlPrecedence
    , map (S.singleton . Prop) ["cbeg", "c", "c", "call", "thr"]
    )
  , ( "Stack trace lang, rejecting Not HierSinceTake"
    , False
    , formulaAt 3 $ Not ((Atomic . Prop $ "c") `HierSinceTake` (Atomic . Prop $ "cbeg"))
    , stlPrecedence
    , map (S.singleton . Prop) ["cbeg", "c", "c", "call", "thr"]
    )
  , ( "Stack trace lang, rejecting HierSinceTake"
    , False
    , formulaAt 3 $ (Not . Atomic . Prop $ "cexc") `HierSinceTake` (Atomic . Prop $ "cbeg")
    , stlPrecedence
    , map (S.singleton . Prop) ["cbeg", "cexc", "c", "call", "thr"]
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
    , ((Atomic . Prop $ "call") `And` (PrecNext (S.singleton Equal) (Atomic . Prop $ "ret"))) `Or` (ChainNext (S.singleton Equal) (Atomic . Prop $ "ret"))
    , stlPrecedence
    , \m -> map (S.singleton . Prop) <$> termTrace m
    )
  , ( "Well formed stack traces, no throw before handle"
    , True
    , Until (S.fromList [Yield, Equal, Take]) (Not . Atomic . Prop $ "thr") (Atomic $ Prop "han")
    , stlPrecedence
    , \m -> map (S.singleton . Prop) <$> termTrace m
    )
  ]

properties :: TestTree
properties = testGroup "QuickCheck tests" (map makePropTest propTuples)
  where makePropTest (name, expected, phi, prec, gen) =
          testProperty name $
            forAll (sized gen) $ \input -> check phi stlPrecedence input == expected

tests :: TestTree
tests = testGroup "Check.hs tests" [unitTests, properties]

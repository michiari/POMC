module TestSat (tests) where

import Test.Tasty
import Test.Tasty.HUnit
import Pomc.Satisfiability
import Pomc.Check (Checkable)
import Pomc.Prec (PrecFunc)
import Pomc.Prop (Prop(..))
import Pomc.PotlV2 (Formula(..), Dir(..))
import Pomc.Example (stlPrecedenceV2)

tests :: TestTree
tests = testGroup "TestSat.hs Tests" $ map makeV2TestCase cases

stlPrecV2sls :: [Prop [Char]]
stlPrecV2sls = map Prop ["call", "ret", "han", "exc"]

makeTestCase :: (Checkable f, Ord a, Show a)
             => (TestName, f a, [Prop a], [Prop a], PrecFunc a, Bool)
             -> TestTree
makeTestCase (name, phi, sls, als, prec, expected) =
  testCase name $ isSatisfiable phi (sls, als) prec @?= expected

makeV2TestCase :: Checkable f =>
                  (TestName, f [Char], [[Char]], Bool) -> TestTree
makeV2TestCase (name, phi, als, expected) =
  makeTestCase (name, phi, stlPrecV2sls, map Prop als, stlPrecedenceV2, expected)

ap :: a -> Formula a
ap = Atomic . Prop

cases :: [([Char], Formula [Char], [[Char]], Bool)]
cases =
  [ ( "First Call"
    , Atomic . Prop $ "call"
    , []
    , True
    ),
    ( "First Not Call"
    , Not . Atomic . Prop $ "call"
    , []
    , True
    ),
    ( "Call and not call"
    , ((Atomic . Prop $ "call") `And` (Not (Atomic . Prop $ "call")))
    , []
    , False
    ),
    ( "Call and ret"
    , ((Atomic . Prop $ "call") `And` (Atomic . Prop $ "ret"))
    , []
    , False
    ),
    ( "Call, next ret 1"
    , ((Atomic . Prop $ "call") `And` (PNext Down (Atomic . Prop $ "ret")))
    , []
    , True
    ),
    ( "Call, next ret 2"
    , ((Atomic . Prop $ "call")
       `And` (PNext Down (Atomic . Prop $ "ret"))
       `And` (PNext Up (Atomic . Prop $ "ret")))
    , []
    , True
    ),
    ( "Call, next down call"
    , ((Atomic . Prop $ "call") `And` (PNext Down (Atomic . Prop $ "call")))
    , []
    , True
    ),
    ( "Call, next up call"
    , ((Atomic . Prop $ "call") `And` (PNext Up (Atomic . Prop $ "call")))
    , []
    , False
    ),
    ( "Exc, back call pa"
    , (PNext Up ((Atomic . Prop $ "exc")
                 `And` (PBack Up (Atomic . Prop $ "call") `And` (Atomic . Prop $ "pa"))))
    , ["pa"]
    , True
    ),
    ( "Matched call 1"
    , (ap "call" `And` (XNext Down (ap "ret")))
    , []
    , True
    ),
    ( "Matched call 2"
    , (ap "call" `And` (XNext Down (ap "ret")) `And` (XNext Up (ap "ret")))
    , []
    , True
    ),
    ( "Impossible downward exc"
    , (ap "call" `And` (XNext Down (ap "exc")))
    , []
    , False
    ),
    ( "Nested calls"
    , (ap "call" `And` (XNext Down (ap "call")))
    , []
    , True
    ),
    ( "Inner call before exc"
    , (ap "call" `And` (XNext Up (ap "exc" `And` (XBack Up $ ap "call"))))
    , []
    , True
    ),
    ( "No han until ret"
    , (ap "call" `And` Until Down (Not . ap $ "han") (ap "ret"))
    , []
    , True
    ),
    ( "No han until down exc"
    , (ap "call" `And` Until Down (Not . ap $ "han") (ap "exc"))
    , []
    , False
    ),
    ( "Next exp, not pa since pb"
    , (ap "call" `And` (XNext Up (ap "exc" `And` (PBack Up $ Since Up (Not . ap $ "pa") (ap "pb")))))
    , ["pa", "pb"]
    , True
    ),
    ( "Call exc and pa in between"
    , (ap "call" `And` (XNext Up (ap "exc")) `And` (PNext Down $ HNext Down (ap "pa")))
    , ["pa"]
    , True
    ),
    ( "Call exc and not pa until pb in between"
    , (ap "call"
       `And` (XNext Up (ap "exc"))
       `And` (PNext Down $ HUntil Down (Not . ap $ "pa") (ap "pb")))
    , ["pa", "pb"]
    , True
    ),
    ( "Nested calls HNext"
    , (ap "call"
       `And` (XNext Down (ap "ret"))
       `And` (XNext Down (HNext Up $ ap "pa")))
    , ["pa"]
    , True
    ),
    ( "Nested calls HUntil"
    , (ap "call"
       `And` (XNext Down (ap "ret"))
       `And` (XNext Down (HUntil Up (ap "pa") (ap "pb"))))
    , ["pa", "pb"]
    , True
    )
  ]

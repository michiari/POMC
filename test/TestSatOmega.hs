module TestSatOmega (tests, cases) where

import Test.Tasty
import Test.Tasty.HUnit
import Pomc.Satisfiability (isSatisfiableGen)
import Pomc.Prec (StructPrecRel)
import Pomc.Prop (Prop(..))
import Pomc.Potl (Formula(..), Dir(..))
import OPMs (stlPrecRelV2, stlPrecV2sls)
import EvalFormulas (ap)
import qualified OmegaEvalFormulas (omegaFormulas)
import qualified Data.Set as S

tests :: TestTree
tests = testGroup "TestSatOmega.hs Tests" [baseTests]

baseTests :: TestTree
baseTests = testGroup "OmegaSat Base Tests" $ map makeV2TestCase cases

evalTests :: TestTree
evalTests = testGroup "OmegaSat Eval Tests" $ map makeV2TestCase OmegaEvalFormulas.omegaFormulas

makeTestCase :: (TestName, Formula String, [Prop String], [Prop String], [StructPrecRel String], Bool)
             -> TestTree
makeTestCase (name, phi, sls, als, prec, expected) =
  let (sat, trace) = isSatisfiableGen True phi (sls, als) prec
      debugMsg False _ = "Expected SAT, got UNSAT."
      debugMsg True tr = "Expected UNSAT, got SAT. Trace:\n" ++ show (map S.toList tr)
  in testCase (name ++ " (" ++ show phi ++ ")") $ assertBool (debugMsg sat trace) (sat == expected)

makeV2TestCase :: (TestName, Formula String, [String], Bool) -> TestTree
makeV2TestCase (name, phi, als, expected) =
  makeTestCase (name, phi, stlPrecV2sls, map Prop als, stlPrecRelV2, expected)

cases :: [(String, Formula String, [String], Bool)]
cases =
  [ 
    ( "Not Always call"
    , Not $ Always $ ap $ "call"
    , []
    , True
    ),
    ( "First Call"
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
    ){-,
    ( "Next exp, not pa since pb"
    , (ap "call" `And` (XNext Up (ap "exc" `And` (PBack Up $ Since Up (Not . ap $ "pa") (ap "pb")))))
    , ["pa", "pb"]
    , True
    ),
    ( "XNext Down HNext Up"
    , (ap "call" `And` (XNext Down (HNext Up $ ap "pa")))
    , ["pa"]
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
    ),
    ( "XNext Down HNext Up perr" --added
    , (ap "call" `And` (XNext Down (HNext Up $ ap "perr")))
    , ["perr"]
    , True
    )-}
  ]
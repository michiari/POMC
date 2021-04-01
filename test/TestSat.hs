module TestSat (tests, cases) where

import Test.Tasty
import Test.Tasty.HUnit
import Pomc.Satisfiability (isSatisfiableGen)
import Pomc.Prec (StructPrecRel)
import Pomc.Prop (Prop(..))
import Pomc.PotlV2 (Formula(..), Dir(..))
import Pomc.Example (stlPrecRelV2, stlPrecV2sls)
import EvalFormulas (ap)
import qualified EvalFormulas (formulas)

tests :: TestTree
tests = testGroup "TestSat.hs Tests" [baseTests]

baseTests :: TestTree
baseTests = testGroup "Sat Base Tests" $ map makeV2TestCase cases

evalTests :: TestTree
evalTests = testGroup "Sat Eval Tests" $ map makeV2TestCase EvalFormulas.formulas

makeTestCase :: (TestName, Formula String, [Prop String], [Prop String], [StructPrecRel String], Bool)
             -> TestTree
makeTestCase (name, phi, sls, als, prec, expected) =
  testCase (name ++ " (" ++ show phi ++ ")") $ isSatisfiableGen True phi (sls, als) prec @?= expected

makeV2TestCase :: (TestName, Formula String, [String], Bool) -> TestTree
makeV2TestCase (name, phi, als, expected) =
  makeTestCase (name, phi, stlPrecV2sls, map Prop als, stlPrecRelV2, expected)

-- only for the finite case
cases :: [(String, Formula String, [String], Bool)]
cases =
  [ ( "First Call"
    , Atomic . Prop $ "call"
    , []
    , True
    )
  ]

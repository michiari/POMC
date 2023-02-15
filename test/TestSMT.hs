module TestSMT ( tests ) where

import EvalFormulas (TestCase, zipExpected, formulas)
import OPMs (stlV2Alphabet)
import Pomc.SMTEncoding (isSatisfiable, SMTResult(..))
import Pomc.Potl (Formula(..), Prop(..))
import Pomc.Prec (Prec(..), StructPrecRel, Alphabet)

import Test.Tasty
import Test.Tasty.HUnit

tests :: TestTree
tests = testGroup "SMTEncoding Satisfiability Tests"
  $ map makeTestCase
  $ zipExpected (filter (isSupported . snd) formulas) expectedRes

makeTestCase :: (TestCase, SMTResult)
             -> TestTree
makeTestCase ((name, phi), expected) =
  let sat = isSatisfiable simpleAlphabet phi
  in testCase (name ++ " (" ++ show phi ++ ")") $ sat >>= (expected @=?)

isSupported :: Formula a -> Bool
isSupported f = case f of
  T             -> True
  Atomic _      -> True
  Not g         -> isSupported g
  Or g h        -> isSupported g && isSupported h
  And g h       -> isSupported g && isSupported h
  Xor g h       -> isSupported g && isSupported h
  Implies g h   -> isSupported g && isSupported h
  Iff g h       -> isSupported g && isSupported h
  PNext _ g     -> isSupported g
  PBack _ _     -> False
  WPNext _ g    -> isSupported g
  XNext _ _     -> False
  XBack _ _     -> False
  WXNext _ _    -> False
  HNext _ _     -> False
  HBack _ _     -> False
  Until _ g h   -> isSupported g && isSupported h
  Release _ g h -> isSupported g && isSupported h
  Since _ _ _   -> False
  HUntil _ _ _  -> False
  HSince _ _ _  -> False
  Eventually _  -> False
  Always _      -> False
  AuxBack _ _   -> False

expectedRes :: [SMTResult]
expectedRes =
  [ Sat, Sat, Unsat, Unsat, Sat, Sat, Sat, Unsat, Sat, Unsat -- base_tests
  , Sat, Sat, Sat, Sat -- contains_exc
  , Sat, Sat -- until_exc
  , Sat, Sat -- until_misc
  ]


simplePrecRel :: [StructPrecRel String]
simplePrecRel = map (\(sl1, sl2, pr) -> (Prop sl1, Prop sl2, pr)) precs
               ++ map (\p -> (Prop p, End, Take)) sl
  where precs = [ ("call", "call", Take) ]
        sl = ["call"]

simpleAlphabet :: Alphabet String
simpleAlphabet = ([Prop "call"], simplePrecRel)

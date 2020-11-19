{-# LANGUAGE QuasiQuotes #-}

module TestMP (tests) where

import Pomc.MiniProcParse (programP)
import Pomc.OpaGen (skeletonsToOpa)
import Pomc.PotlV2 (Formula)
import Pomc.ModelChecker (modelCheckGen)
import qualified TestSat (cases)
import EvalFormulas (formulas)

import Test.Tasty
import Test.Tasty.HUnit
import Text.Megaparsec
import Text.RawString.QQ
import qualified Data.Text as T

tests :: TestTree
tests = testGroup "MiniProc Tests" [sasBaseTests, sasEvalTests]

sasBaseTests :: TestTree
sasBaseTests = testGroup "SAS MiniProc MC Base Tests" $
  map (makeTestCase sasMPSource) (zip TestSat.cases expectedSasBase)

sasEvalTests :: TestTree
sasEvalTests = testGroup "SAS MiniProc MC Eval Tests" $
  map (makeTestCase sasMPSource) (zip EvalFormulas.formulas expectedSasEval)


makeTestCase :: T.Text
             -> ((String, Formula String, [String], Bool), Bool)
             -> TestTree
makeTestCase filecont ((name, phi, _, _), expected) =
  testCase (name ++ " (" ++ show phi ++ ")") assertion
  where assertion = do
          prog <- case parse programP "" filecont of
                    Left  errBundle -> assertFailure (errorBundlePretty errBundle)
                    Right fsks      -> return fsks
          modelCheckGen (fmap T.pack phi) (skeletonsToOpa prog) @?= expected


expectedSasBase :: [Bool]
expectedSasBase = [True, False, False, False, False, False,
                   False, False, False, True, True, False,
                   True, False, True, False, False, False,
                   False, False, False, False
                  ]

expectedSasEval :: [Bool]
expectedSasEval = [True, True, True, True,     -- chain_next
                   True, False,                -- contains_exc
                   True,                       -- data_access
                   False, False, True,         -- empty_frame
                   True,                       -- exception_safety
                   False, False, False, False, -- hier_down
                   False,                      -- hier_insp
                   True,                       -- hier_insp_exc
                   True, True, False, False,   -- hier_up
                   False, False,               -- normal_ret
                   True, True,                 -- no_throw
                   True, True,                 -- stack_inspection
                   False,                      -- uninstall_han
                   False, True, True,          -- until_exc
                   True, True, False           -- until_misc
                  ]

sasMPSource :: T.Text
sasMPSource = T.pack [r|pa() {
  try {
    pb();
  } catch {
    perr();
    perr();
  }
}

pb() {
  pc();
}

pc() {
  if {
    throw;
  } else {
    pc();
  }
}

perr() { }
|]

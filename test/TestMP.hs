{-# LANGUAGE QuasiQuotes #-}

module TestMP (tests) where

import Pomc.MiniProcParse (programP)
import Pomc.MiniProc (programToOpa)
import Pomc.Potl (Formula(..), Dir(..))
import Pomc.ModelChecker (modelCheckGen)
import qualified TestSat (cases)
import EvalFormulas (ap, formulas)

import Test.Tasty
import Test.Tasty.HUnit
import Text.Megaparsec
import Text.RawString.QQ
import qualified Data.Text as T

tests :: TestTree
tests = testGroup "MiniProc Tests" [ sasBaseTests, sasEvalTests
                                   , noHanBaseTests, noHanEvalTests
                                   , simpleThenBaseTests, simpleThenEvalTests
                                   , simpleElseBaseTests, simpleElseEvalTests
                                   , singleWhile
                                   , exprsTests
                                   , jensenTests
                                   ]

sasBaseTests :: TestTree
sasBaseTests = testGroup "SAS MiniProc MC Base Tests" $
  map (makeTestCase sasMPSource) (zip TestSat.cases expectedSasBase)

sasEvalTests :: TestTree
sasEvalTests = testGroup "SAS MiniProc MC Eval Tests" $
  map (makeTestCase sasMPSource) (zip EvalFormulas.formulas expectedSasEval)

noHanBaseTests :: TestTree
noHanBaseTests = testGroup "NoHan MiniProc MC Base Tests" $
  map (makeTestCase noHanSource) (zip TestSat.cases expectedNoHanBase)

noHanEvalTests :: TestTree
noHanEvalTests = testGroup "NoHan MiniProc MC Eval Tests" $
  map (makeTestCase noHanSource) (zip EvalFormulas.formulas expectedNoHanEval)

simpleThenBaseTests :: TestTree
simpleThenBaseTests = testGroup "SimpleThen MiniProc MC Base Tests" $
  map (makeTestCase simpleThenSource) (zip TestSat.cases expectedSimpleThenBase)

simpleThenEvalTests :: TestTree
simpleThenEvalTests = testGroup "SimpleThen MiniProc MC Eval Tests" $
  map (makeTestCase simpleThenSource) (zip EvalFormulas.formulas expectedSimpleThenEval)

simpleElseBaseTests :: TestTree
simpleElseBaseTests = testGroup "SimpleElse MiniProc MC Base Tests" $
  map (makeTestCase simpleElseSource) (zip TestSat.cases expectedSimpleElseBase)

simpleElseEvalTests :: TestTree
simpleElseEvalTests = testGroup "SimpleElse MiniProc MC Eval Tests" $
  map (makeTestCase simpleElseSource) (zip EvalFormulas.formulas expectedSimpleElseEval)

makeTestCase :: T.Text
             -> ((String, Formula String, [String], Bool), Bool)
             -> TestTree
makeTestCase filecont ((name, phi, _, _), expected) =
  testCase (name ++ " (" ++ show phi ++ ")") assertion
  where assertion = do
          prog <- case parse (programP <* eof) name filecont of
                    Left  errBundle -> assertFailure (errorBundlePretty errBundle)
                    Right fsks      -> return fsks
          fst (modelCheckGen (fmap T.pack phi) (programToOpa prog)) @?= expected


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
sasMPSource = T.pack [r|
pa() {
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
  if (*) {
    throw;
  } else {
    pc();
  }
}

perr() { }
|]

expectedNoHanBase :: [Bool]
expectedNoHanBase = [True, False, False, False, False, False,
                     True, False, False, False, False, False,
                     False, True, False, False, False, False,
                     False, True, False, False
                    ]

expectedNoHanEval :: [Bool]
expectedNoHanEval = [False, False, False, True,  -- chain_next
                     False, False,               -- contains_exc
                     True,                       -- data_access
                     False, False, False,        -- empty_frame
                     False,                      -- exception_safety
                     True, False, False, False,  -- hier_down
                     False,                      -- hier_insp
                     True,                       -- hier_insp_exc
                     False, False, False, False, -- hier_up
                     False, False,               -- normal_ret
                     False, False,               -- no_throw
                     True, True,                 -- stack_inspection
                     True,                       -- uninstall_han
                     True, True, False,          -- until_exc
                     False, False, False         -- until_misc
                  ]

noHanSource :: T.Text
noHanSource = T.pack [r|
pa() {
  pb();
}

pb() {
  pc();
}

pc() {
  if (*) {
    throw;
  } else {
    pc();
  }
}
|]


expectedSimpleThenBase :: [Bool]
expectedSimpleThenBase = [True, False, False, False, False, False,
                          False, False, False, True, True, False,
                          True, False, True, False, False, False,
                          False, False, False, False
                         ]

expectedSimpleThenEval :: [Bool]
expectedSimpleThenEval = [False, False, False, False, -- chain_next
                          True, False,                -- contains_exc
                          True,                       -- data_access
                          False, False, True,         -- empty_frame
                          True,                       -- exception_safety
                          False, False, False, False, -- hier_down
                          False,                      -- hier_insp
                          True,                       -- hier_insp_exc
                          False, False, False, False, -- hier_up
                          False, False,               -- normal_ret
                          True, True,                 -- no_throw
                          True, True,                 -- stack_inspection
                          False,                      -- uninstall_han
                          False, False, False,        -- until_exc
                          False, True, False          -- until_misc
                         ]

simpleThenSource :: T.Text
simpleThenSource = T.pack [r|
var foo;

pa() {
  foo = true;
  try {
    pb();
  } catch {
    pc();
  }
}

pb() {
  if (foo) {
    throw;
  } else {}
}

pc() { }
|]


expectedSimpleElseBase :: [Bool]
expectedSimpleElseBase = [True, False, False, False, False, False,
                          False, False, False, True, True, False,
                          False, False, True, False, False, False,
                          False, False, False, False
                         ]

expectedSimpleElseEval :: [Bool]
expectedSimpleElseEval = [False, False, False, False, -- chain_next
                          True, False,                -- contains_exc
                          True,                       -- data_access
                          False, False, False,        -- empty_frame
                          True,                       -- exception_safety
                          False, False, False, False, -- hier_down
                          False,                      -- hier_insp
                          True,                       -- hier_insp_exc
                          False, False, False, False, -- hier_up
                          False, True,                -- normal_ret
                          True, True,                 -- no_throw
                          True, True,                 -- stack_inspection
                          False,                      -- uninstall_han
                          False, False, True,         -- until_exc
                          False, False, False         -- until_misc
                         ]

simpleElseSource :: T.Text
simpleElseSource = T.pack [r|
var foo;

pa() {
  foo = false;
  try {
    pb();
  } catch {
    pc();
  }
}

pb() {
  if (foo) {
    throw;
  } else {}
}

pc() { }
|]


singleWhile :: TestTree
singleWhile = makeTestCase simpleWhileSource
  (("Single-Iteration While Loop"
   , Not $ Until Down T (ap "call"
                         `And` ap "pb"
                         `And` (HNext Up $ HUntil Up T (ap "call" `And` ap "pb")))
   , []
   , True)
  , True)

simpleWhileSource :: T.Text
simpleWhileSource = T.pack [r|
var foo;

pa() {
  foo = true;
  while (foo) {
    pb();
    foo = false;
  }
}

pb() {}
|]


exprsTests :: TestTree
exprsTests = testGroup "BoolExpr Tests" [exprsPb, exprsPc, exprsPd]

exprsPb :: TestTree
exprsPb = makeTestCase exprsSource
  (("Check Or BoolExpr"
   , Until Down T (ap "call" `And` ap "pb")
   , []
   , True)
  , True)

exprsPc :: TestTree
exprsPc = makeTestCase exprsSource
  (("Check Or Not BoolExpr"
   , Until Down T (ap "call" `And` ap "pc")
   , []
   , True)
  , True)

exprsPd :: TestTree
exprsPd = makeTestCase exprsSource
  (("Check And Not BoolExpr"
   , Until Down T (ap "call" `And` ap "pd")
   , []
   , False)
  , False)

exprsSource :: T.Text
exprsSource = T.pack [r|
var foo, bar;

pa() {
  foo = true;
  bar = false;
  foo = !(foo || bar);
  bar = !(foo && bar);
  if (foo || bar) {
    pb();
  } else {}
  if (!foo) {
    pc();
  } else {}
  if (!bar) {
    pd();
  } else {}
}

pb() {}
pc() {}
pd() {}
|]

jensenTests :: TestTree
jensenTests = testGroup "Jensen Privileges Tests" [ jensenRd, jensenWr
                                                  , jensenRdCp, jensenWrDb
                                                  ]

jensenRd :: TestTree
jensenRd = makeTestCase jensen
  (("Only privileged reads."
   , Always $ ((ap "call" `And` ap "raw_read")
                `Implies`
                (Not $ Since Down T
                  (ap "call"
                   `And` (Not $ ap "P_rd")
                   `And` (Not $ ap "raw_read")
                   `And` (Not $ ap "main"))))
   , []
   , True)
  , True)

jensenWr :: TestTree
jensenWr = makeTestCase jensen
  (("Only privileged writes."
   , Always $ ((ap "call" `And` ap "raw_write")
                `Implies`
                (Not $ Since Down T
                  (ap "call"
                   `And` (Not $ ap "P_wr")
                   `And` (Not $ ap "raw_write")
                   `And` (Not $ ap "main"))))
   , []
   , True)
  , True)

jensenRdCp :: TestTree
jensenRdCp = makeTestCase jensen
  (("Only reads with canpay privilege."
   , Always $ ((ap "call" `And` ap "raw_read")
                `Implies`
                (Not $ Since Down T
                  (ap "call"
                   `And` (Not $ ap "P_cp")
                   `And` (Not $ ap "raw_read")
                   `And` (Not $ ap "main"))))
   , []
   , True)
  , True)

jensenWrDb :: TestTree
jensenWrDb = makeTestCase jensen
  (("Only writes with debit privilege."
   , Always $ ((ap "call" `And` ap "raw_write")
                `Implies`
                (Not $ Since Down T
                  (ap "call"
                   `And` (Not $ ap "P_db")
                   `And` (Not $ ap "raw_write")
                   `And` (Not $ ap "main"))))
   , []
   , True)
  , True)

jensen :: T.Text
jensen = T.pack [r|
var P_cp, P_db, P_rd, P_wr, CP;

main() {
  P_cp = true;
  P_db = true;
  P_rd = true;
  P_wr = true;
  CP = false;
  spender();

  P_cp = false;
  P_db = false;
  P_rd = false;
  P_wr = false;
  clyde();
}

spender() {
  account.canpay();
  if (P_cp) {
    account.debit();
  } else {}

  if (*) {
    spender();
  } else {}
}

clyde() {
  account.debit();
  if (*) {
    clyde();
  } else {}
}

account.canpay() {
  if (P_cp) {
    read();
    CP = true;
  } else {
    throw;
  }
}

account.debit() {
  if (P_db) {
    account.canpay();
    if (CP) {
      write();
      CP = false;
    } else {
      throw;
    }
  } else {
    throw;
  }
}

read() {
  if (P_rd) {
    raw_read();
  } else {
    throw;
  }
}

write() {
  if (P_wr) {
    raw_write();
  } else {
    throw;
  }
}

raw_read() {}
raw_write() {}
|]

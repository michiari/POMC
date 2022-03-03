{-# LANGUAGE QuasiQuotes #-}

module TestMP (tests) where

import Pomc.MiniProcParse (programP)
import Pomc.Potl (Formula(..), Dir(..))
import Pomc.ModelChecker (modelCheckProgram)
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
                                   , generic
                                   , jensenTests
                                   , stackTests
                                   , intTests
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


-- only for the finite case
makeTestCase :: T.Text
             -> ((String, Formula String, Bool), Bool)
             -> TestTree
makeTestCase filecont ((name, phi, _), expected) =
  testCase (name ++ " (" ++ show phi ++ ")") assertion
  where assertion = do
          prog <- case parse (programP <* eof) name filecont of
                    Left  errBundle -> assertFailure (errorBundlePretty errBundle)
                    Right fsks      -> return fsks
          fst (modelCheckProgram False (fmap T.pack phi) prog) @?= expected


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
                   True, True, True            -- until_misc
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
bool foo;

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
bool foo;

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
   , True)
  , True)

simpleWhileSource :: T.Text
simpleWhileSource = T.pack [r|
bool foo;

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
   , True)
  , True)

exprsPc :: TestTree
exprsPc = makeTestCase exprsSource
  (("Check Or Not BoolExpr"
   , Until Down T (ap "call" `And` ap "pc")
   , True)
  , True)

exprsPd :: TestTree
exprsPd = makeTestCase exprsSource
  (("Check And Not BoolExpr"
   , Until Down T (ap "call" `And` ap "pd")
   , False)
  , False)

exprsSource :: T.Text
exprsSource = T.pack [r|
bool foo, bar;

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


-- Tests from POTL paper

generic :: TestTree
generic = testGroup "MiniProc Generic Tests" [genSmall, genMed, genLarge]

genSmall :: TestTree
genSmall = makeTestCase sasMPSource
  (("MiniProc Generic Small"
   , Always $ (ap "call" `And` ap "pb" `And` (Since Down T (ap "call" `And` ap "pa")))
     `Implies` (PNext Up (ap "exc") `Or` XNext Up (ap "exc"))
   , True)
  , True)

genMed :: TestTree
genMed = makeTestCase genMedSource
  (("MiniProc Generic Medium"
   , Always $ (ap "call" `And` ap "pb" `And` (Since Down T (ap "call" `And` ap "pa")))
     `Implies` (PNext Up (ap "exc") `Or` XNext Up (ap "exc"))
   , False)
  , False)

genMedSource :: T.Text
genMedSource = T.pack [r|
pa() {
  pb();
  try {
    pc();
  } catch {
    perr();
  }
}

pb() {
  if (*) {
    pc();
  } else {
    try {
      pc();
    } catch {
      perr();
    }
  }
}

pc() {
  if (*) {
    pb();
  } else {
    throw;
  }
}

perr() {
  if (*) {
    perr();
  } else {}
}
|]

genLarge :: TestTree
genLarge = makeTestCase genLargeSource
  (("MiniProc Generic Large"
   , Always $ (ap "call" `And` ap "pb" `And` (Since Down T (ap "call" `And` ap "pa")))
     `Implies` (PNext Up (ap "exc") `Or` XNext Up (ap "exc"))
   , True)
  , True)

genLargeSource :: T.Text
genLargeSource = T.pack [r|
main() {
       pa();
       try {
           pa();
           pb();
       } catch {
           perr();
       }
}

pa() {
     pc();
     pd();
     if (*) {
        pa();
     } else {}
}

pb() {
     try {
         pe();
     } catch {
         perr();
     }
}

pc() {
     if (*) {
        pa();
     } else {
        pe();
     }
}

pd() {
     pc();
     pa();
}

pe() {
     if (*) {
        throw;
     } else {}
}

perr() {}
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
   , True)
  , True)

jensen :: T.Text
jensen = T.pack [r|
bool P_cp, P_db, P_rd, P_wr, CP;

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


stackTests :: TestTree
stackTests = testGroup "MiniProc Stack Tests" [ stackUnsafe, stackUnsafeNeutrality
                                              , stackSafe, stackSafeNeutrality]

stackUnsafe :: TestTree
stackUnsafe = makeTestCase stackUnsafeSource
  (("MiniProc Unsafe Stack"
   , Always $ (ap "exc"
               `Implies`
               (Not $ (PBack Up (ap "tainted")
                       `Or` XBack Up (ap "tainted" `And` Not (ap "main")))
                `And` XBack Up (ap "Stack::push" `Or` ap "Stack::pop")))
   , False)
  , False)

stackUnsafeNeutrality :: TestTree
stackUnsafeNeutrality = makeTestCase stackUnsafeSource
  (("MiniProc Unsafe Stack Neutrality"
   , Always ((ap "exc"
              `And` PBack Up (ap "T")
              `And` XBack Down (ap "han" `And` XBack Down (ap "Stack")))
              `Implies`
              (XBack Down $ XBack Down $ XNext Up $ ap "exc"))
     , True)
  , True)

stackUnsafeSource :: T.Text
stackUnsafeSource = T.pack [r|
bool tainted;

main() {
  tainted = false;

  Stack::Stack();

  T::T();
  Stack::push();

  tainted = false;
  T::T();
  Stack::push();

  tainted = false;
  Stack::size();
  Stack::pop();

  tainted = false;
  T::Tcp();

  Stack::~Stack();
  T::~T();
}

Stack::Stack() {
  T::operator_new();
}

Stack::~Stack() {
  T::operator_delete();
}

Stack::Stackcp() {
  Stack::NewCopy();
}

Stack::operator=() {
  if (*) {
    Stack::NewCopy();
    T::operator_delete();
  } else {}
}

Stack::push() {
  if (*) {
    Stack::NewCopy();
    T::operator_delete();
  } else {}
  tainted = true;
  T::operator=();
}

Stack::pop() {
  if (*) {
    throw;
  } else {
    tainted = true;
    T::Tcp();
  }
}

Stack::size() {}

Stack::NewCopy() {
  T::operator_new();
  try {
    std::copy();
  } catch {
    T::operator_delete();
    throw;
  }
}

T::T() {
  if (*) {
    throw;
  } else {}
}

T::Tcp() {
  if (*) {
    throw;
  } else {}
}

T::operator_new() {
  if (*) {
    throw;
  } else {
    while (*) {
      T::T();
    }
  }
}

T::operator=() {
  if (*) {
    throw;
  } else {}
}

T::operator_delete() {}
T::~T() {}

std::copy() {
  T::operator=();
}
|]


stackSafe :: TestTree
stackSafe = makeTestCase stackSafeSource
  (("MiniProc Safe Stack"
   , Always $ (ap "exc"
               `Implies`
               (Not $ (PBack Up (ap "tainted")
                       `Or` XBack Up (ap "tainted" `And` Not (ap "main")))
                `And` XBack Up (ap "Stack::push" `Or` ap "Stack::pop")))
   , True)
  , True)

stackSafeNeutrality :: TestTree
stackSafeNeutrality = makeTestCase stackSafeSource
  (("MiniProc Safe Stack Neutrality"
   , Always ((ap "exc"
              `And` PBack Up (ap "T")
              `And` XBack Down (ap "han" `And` XBack Down (ap "Stack")))
              `Implies`
              (XBack Down $ XBack Down $ XNext Up $ ap "exc"))
     , True)
  , True)

stackSafeSource :: T.Text
stackSafeSource = T.pack [r|
bool tainted, full;

main() {
  tainted = false;
  full = false;

  Stack::Stack();

  T::T();
  Stack::push();

  tainted = false;
  full = true;
  T::T();
  Stack::push();

  tainted = false;
  Stack::size();
  Stack::pop();

  tainted = false;
  T::Tcp();

  Stack::~Stack();
  T::~T();
}

StackImpl::StackImpl() {
  _::operator_new();
}

StackImpl::~StackImpl() {
  std::destroy();
  _::operator_delete();
}

StackImpl::swap() {
  std::swap();
  std::swap();
  std::swap();
}

Stack::Stack() {
  StackImpl::StackImpl();
}

Stack::Stackcp() {
  StackImpl::StackImpl();
  while (*) {
    std::construct();
  }
}

Stack::operator=() {
  Stack::Stackcp();
  StackImpl::swap();
}

Stack::size() {}

Stack::push() {
  if (full) {
    Stack::Stack();
    full = false;
    while (*) {
      Stack::push();
    }
    Stack::push();
    StackImpl::swap();
  } else {
    std::construct();
  }
}

Stack::top() {
  if (*) {
    throw;
  } else {
    T::Tcp();
  }
}

Stack::pop() {
  if (*) {
    throw;
  } else {
    std::destroy();
  }
}

Stack::~Stack() {
  StackImpl::StackImpl();
}

T::T() {
  if (*) {
    throw;
  } else {}
}

T::Tcp() {
  if (*) {
    throw;
  } else {}
}

T::operator_new() {
  if (*) {
    throw;
  } else {
    while (*) {
      T::T();
    }
  }
}

T::operator=() {
  if (*) {
    throw;
  } else {}
}

T::~T() {}

std::swap() {
  tainted = true;
}

std::construct() {
  while (*) {
    T::Tcp();
  }
}

std::destroy() {
  while (*) {
    T::~T();
  }
}

_::operator_new() {
  if (*) {
    throw;
  } else {}
}
_::operator_delete() {}
|]


intTests :: TestTree
intTests = testGroup "Int Variables Tests" [ u8Arith1Tests
                                           , u8Arith2Tests
                                           , arithCastsTests
                                           , nondetTests
                                           , arrayTests
                                           , arrayLoopTests
                                           ]

u8Arith1Tests :: TestTree
u8Arith1Tests = testGroup "u8Arith1" [ u8Arith1Exc, u8Arith1Ret, u8Arith1aHolds ]

u8Arith1Exc :: TestTree
u8Arith1Exc = makeTestCase u8Arith1Src
  (("Throws."
   , Until Up T (ap "exc")
   , True)
  , True)

u8Arith1Ret :: TestTree
u8Arith1Ret = makeTestCase u8Arith1Src
  (("Terminates normally."
   , Until Up T (ap "ret")
   , False)
  , False)

u8Arith1aHolds :: TestTree
u8Arith1aHolds = makeTestCase u8Arith1Src
  (("Variable a is non-zero at the end."
   , XNext Up (ap "a")
   , True)
  , True)

u8Arith1Src :: T.Text
u8Arith1Src = T.pack [r|
u8 a, b, c;

main() {
  a = 4u8;
  b = 5u8;
  c = a * b;
  if (a >= c / 5u8) {
    throw;
  } else { }
}
|]

u8Arith2Tests :: TestTree
u8Arith2Tests = testGroup "u8Arith2" [ u8Arith2Ret, u8Arith2Assert, u8Arith2AssertFalse ]

u8Arith2Ret :: TestTree
u8Arith2Ret = makeTestCase u8Arith2Src
  (("Terminates normally."
   , Until Up T (ap "ret")
   , True)
  , True)

u8Arith2Assert :: TestTree
u8Arith2Assert = makeTestCase u8Arith2Src
  (("Assert true."
   , Until Up T (ap "ret" `And` ap "assert")
   , True)
  , True)

u8Arith2AssertFalse :: TestTree
u8Arith2AssertFalse = makeTestCase u8Arith2Src
  (("Assert false."
   , Until Up T (ap "ret" `And` (Not $ ap "assert"))
   , False)
  , False)

u8Arith2Src :: T.Text
u8Arith2Src = T.pack [r|
u8 a, b, x, y, assert;

main() {
  x = 1u8;
  y = 10u8;
  a = 4u8;
  b = 2u8;
  if (x > 0u8) {
    b = a + 2u8;
    if (x < y) {
      a = (x * 2u8) + y;
    } else { }
  } else { }
  assert = a != b;
}
|]


arithCastsTests :: TestTree
arithCastsTests = testGroup "ArithCasts" [ arithCastsAssert1
                                         , arithCastsAssert2
                                         , arithCastsAssert3
                                         , arithCastsAssert4
                                         , arithCastsAssert5
                                         ]

arithCastsAssert1 :: TestTree
arithCastsAssert1 = makeTestCase arithCastsSrc
  (("a + c > 1024u16"
   , Until Down T (ap "ret" `And` ap "assert1")
   , True)
  , True)

arithCastsAssert2 :: TestTree
arithCastsAssert2 = makeTestCase arithCastsSrc
  (("b + d < 0s8"
   , Until Down T (ap "ret" `And` ap "assert2")
   , True)
  , True)

arithCastsAssert3 :: TestTree
arithCastsAssert3 = makeTestCase arithCastsSrc
  (("f == 25u8"
   , Until Down T (ap "ret" `And` ap "assert3")
   , True)
  , True)

arithCastsAssert4 :: TestTree
arithCastsAssert4 = makeTestCase arithCastsSrc
  (("b * c == 10240s16"
   , Until Down T (ap "ret" `And` ap "assert4")
   , True)
  , True)

arithCastsAssert5 :: TestTree
arithCastsAssert5 = makeTestCase arithCastsSrc
  (("d / b == -1s8"
   , Until Down T (ap "ret" `And` ap "assert5")
   , True)
  , True)

arithCastsSrc :: T.Text
arithCastsSrc = T.pack [r|
u8 a, b, f;
s16 c, d;
s32 e;
bool assert1, assert2, assert3, assert4, assert5;

main() {
  a = 255u8;
  b = 10u8;
  c = 1024s16;
  d = -15s8;

  assert1 = a + c > 1024u16;
  assert2 = b + d < 0s8;

  f = b - d;
  assert3 = f == 25u8;

  assert4 = b * c == 10240s16;
  assert5 = d / b == -1s8;
}
|]

nondetTests :: TestTree
nondetTests = testGroup "Nondeterministic Int" [ nondetCover0
                                               , nondetCover1
                                               , nondetCover2
                                               , nondetAssert
                                               ]

nondetCover0 :: TestTree
nondetCover0 = makeTestCase nondetSrc
  (("Coverage 0"
   , XNext Down (ap "ret" `And` (Not $ ap "cover0"))
   , False)
  , False)

nondetCover1 :: TestTree
nondetCover1 = makeTestCase nondetSrc
  (("Coverage 1"
   , XNext Down (ap "ret" `And` (Not $ ap "cover1"))
   , False)
  , False)

nondetCover2 :: TestTree
nondetCover2 = makeTestCase nondetSrc
  (("Coverage 2"
   , XNext Down (ap "ret" `And` (Not $ ap "cover2"))
   , False)
  , False)

nondetAssert :: TestTree
nondetAssert = makeTestCase nondetSrc
  (("Assert true."
   , Until Up T (ap "ret" `And` ap "assert")
   , True)
  , True)

nondetSrc :: T.Text
nondetSrc = T.pack [r|
u8 a, b, x, y;
bool assert, cover0, cover1, cover2;

main() {
  x = *;
  y = 10u8;
  a = 4u8;
  b = 2u8;
  if (x > 0u8) {
    b = a + 2u8;
    if (x < y) {
      a = (x * 2u8) + y;
      cover0 = true;
    } else {
      cover1 = true;
    }
  } else {
    cover2 = true;
  }
  assert = a != b;
}
|]


arrayTests :: TestTree
arrayTests = testGroup "Int Array Tests" [ arrayCover0
                                         , arrayCover1
                                         , arrayAssert0
                                         ]

arrayCover0 :: TestTree
arrayCover0 = makeTestCase arraySrc
  (("Coverage 0"
   , XNext Down (ap "ret" `And` (Not $ ap "cover0"))
   , False)
  , False)

arrayCover1 :: TestTree
arrayCover1 = makeTestCase arraySrc
  (("Coverage 1"
   , XNext Down (ap "ret" `And` (Not $ ap "cover1"))
   , False)
  , False)

arrayAssert0 :: TestTree
arrayAssert0 = makeTestCase arraySrc
  (("Assert 0"
   , XNext Down (ap "ret" `And` ap "assert0")
   , True)
  , True)

arraySrc :: T.Text
arraySrc = T.pack [r|
s8[4] foo;
u4[2] bar;
bool cover0, cover1, assert0;

main() {
  foo[1u8] = 6s8;
  foo[3u8] = 7s8;
  bar[0u8] = *;
  bar[1u8] = foo[3u8] - foo[1u8];
  foo[2u8] = foo[1u8] + bar[0u8];

  if (foo[2u8] > 10s8) {
    cover0 = true;
  } else {
    cover1 = true;
  }

  assert0 = foo[0u8] + bar[0u8] == bar[0u8];
}
|]


arrayLoopTests :: TestTree
arrayLoopTests = testGroup "Int Array Loop Tests" [ arrayLoopAssert0 ]

arrayLoopAssert0 :: TestTree
arrayLoopAssert0 = makeTestCase arrayLoopSrc
  (("Assert 0"
   , XNext Down (ap "ret" `And` ap "assert0")
   , True)
  , True)

arrayLoopSrc :: T.Text
arrayLoopSrc = T.pack [r|
u8[10] numbers;
u8 i, n, acc;
bool assert0;

main() {
  n = 10u8;
  i = 0u8;
  while (i < n) {
    numbers[i] = i;
    i = i + 1u8;
  }

  acc = 0u8;
  i = 0u8;
  while (i < n) {
    acc = acc + numbers[i];
    i = i + 1u8;
  }

  assert0 = acc == (n * (n - 1u8)) / 2u8;
}
|]

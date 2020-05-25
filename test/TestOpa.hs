module TestOpa (tests) where

import Test.Tasty
import Test.Tasty.HUnit

import POMC.Prec (Prec(..))
import POMC.Opa (Opa(..), runOpa)
import POMC.Util (lookupOrDefault)

arithOpa :: Opa Int Char
arithOpa =
  Opa { alphabet   = "+xn()"
      , prec       = (\t1 t2 -> lookup (t1, t2) arithOpaPrecMatrix)
      , states     = [0, 1, 2, 3]
      , initials   = [0]
      , finals     = [1, 3]
      , deltaShift = (\s  t  -> lookupOrDefault (s,  t)  arithOpaDeltaShift [])
      , deltaPush  = (\s  t  -> lookupOrDefault (s,  t)  arithOpaDeltaPush  [])
      , deltaPop   = (\s1 s2 -> lookupOrDefault (s1, s2) arithOpaDeltaPop   [])
      }
  where
    arithOpaPrecMatrix =
      [ (('+', '+'), Take)
      , (('+', 'x'), Yield)
      , (('+', '('), Yield)
      , (('+', ')'), Take)
      , (('+', 'n'), Yield)

      , (('x', '+'), Take)
      , (('x', 'x'), Take)
      , (('x', '('), Yield)
      , (('x', ')'), Take)
      , (('x', 'n'), Yield)

      , (('(', '+'), Yield)
      , (('(', 'x'), Yield)
      , (('(', '('), Yield)
      , (('(', ')'), Equal)
      , (('(', 'n'), Yield)

      , ((')', '+'), Take)
      , ((')', 'x'), Take)
      , ((')', ')'), Take)

      , (('n', '+'), Take)
      , (('n', 'x'), Take)
      , (('n', ')'), Take)
      ]
    arithOpaDeltaShift = [((3, ')'), [3])]
    arithOpaDeltaPush =
      [ ((0, 'n'), [1])
      , ((0, '('), [2])

      , ((1, '+'), [0])
      , ((1, 'x'), [0])

      , ((2, '('), [2])
      , ((2, 'n'), [3])

      , ((3, '+'), [2])
      , ((3, 'x'), [2])
      ]
    arithOpaDeltaPop =
      [ ((1, 0), [1])
      , ((1, 1), [1])

      , ((3, 0), [3])
      , ((3, 1), [3])
      , ((3, 2), [3])
      , ((3, 3), [3])
      ]

vcOpa :: Opa [Char] [Char]
vcOpa =
  Opa { alphabet   = ["sv", "rb", "wr", "ud"]
      , prec       = (\t1 t2 -> lookup (t1, t2) vcOpaPrecMatrix)
      , states     = ["q0", "q1", "q4", "0", "1", "2"]
      , initials   = ["q0"]
      , finals     = ["q0"]
      , deltaShift = (\s  t  -> lookupOrDefault (s,  t)  vcOpaDeltaShift [])
      , deltaPush  = (\s  t  -> lookupOrDefault (s,  t)  vcOpaDeltaPush  [])
      , deltaPop   = (\s1 s2 -> lookupOrDefault (s1, s2) vcOpaDeltaPop   [])
      }
  where
    vcOpaPrecMatrix =
      [ (("sv", "sv"), Yield)
      , (("sv", "rb"), Equal)
      , (("sv", "wr"), Yield)

      , (("rb", "sv"), Take)
      , (("rb", "rb"), Take)
      , (("rb", "wr"), Take)
      , (("rb", "ud"), Take)

      , (("wr", "sv"), Yield)
      , (("wr", "rb"), Take)
      , (("wr", "wr"), Yield)
      , (("wr", "ud"), Equal)

      , (("ud", "sv"), Take)
      , (("ud", "rb"), Take)
      , (("ud", "wr"), Take)
      , (("ud", "ud"), Take)
      ]

    vcOpaDeltaShift =
      [ (("q4", "ud"), ["q4"])

      , (("0",  "rb"), ["q1"])
      ]

    vcOpaDeltaPush =
      [ (("q0", "sv"), ["0"])

      , (("q4",  "wr"), ["q4"])

      , (("0",  "sv"), ["0"])
      , (("0",  "wr"), ["1", "q4"])

      , (("1",  "sv"), ["0"])
      , (("1",  "wr"), ["2", "q4"])

      , (("2",  "sv"), ["0"])
      , (("2",  "wr"), ["q4"])
      ]

    vcOpaDeltaPop =
      [ (("q0",  "q0"), ["q0"])
      , (("q0",   "0"), ["q0"])
      , (("q0",   "1"), ["q0"])

      , (("q1", "q0"), ["q0"])
      , (("q1",  "0"),  ["0"])
      , (("q1",  "1"),  ["1"])
      , (("q1",  "2"),  ["2"])

      , (("q4", "q4"), ["q4"])
      , (("q4",  "0"),  ["0"])
      , (("q4",  "1"),  ["1"])
      , (("q4",  "2"),  ["2"])

      , (("0", "q0"), ["q0"])
      , (("0",  "0"), ["q0"])
      , (("0",  "1"), ["q0"])
      , (("0",  "2"), ["q0"])

      , (("1", "0"), ["0"])

      , (("2", "1"), ["1"])
      ]

tests :: TestTree
tests = testGroup "Opa.hs tests"
  [ testCase "Arithmetic OPA run with \"(n+n)xn\"" $
      runOpa arithOpa "(n+n)xn" @? acceptFail

  , testCase "Arithmetic OPA run with \"(+\"" $
      not (runOpa arithOpa "(+") @? rejectFail

  , testCase "Arithmetic OPA run with empty input" $
      not (runOpa arithOpa "") @? rejectFail

  , testCase "VC OPA run with \"sv wr ud rb sv wr wr ud sv wr rb wr sv\"" $
      runOpa vcOpa (words "sv wr ud rb sv wr wr ud sv wr rb wr sv") @? acceptFail

  , testCase "VC OPA run with \"sv wr wr wr sv\"" $
      not (runOpa vcOpa $ words "sv wr wr wr sv") @? rejectFail

  , testCase "VC OPA run with empty input" $
      runOpa vcOpa [] @? acceptFail
  ]
  where acceptFail = "Automaton should accept!"
        rejectFail  = "Automaton should reject!"

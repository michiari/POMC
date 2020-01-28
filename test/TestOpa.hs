module TestOpa (tests) where

import Test.Tasty
import Test.Tasty.HUnit

import POMC.Opa
import POMC.Util

arithOpa :: Opa Int Char
arithOpa =
  let
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
      , ((')', '('), Equal) -- not needed
      , ((')', ')'), Take)
      , ((')', 'n'), Equal) -- not needed

      , (('n', '+'), Take)
      , (('n', 'x'), Take)
      , (('n', '('), Equal) -- not needed
      , (('n', ')'), Take)
      , (('n', 'n'), Equal) -- not needed
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
  in Opa
    "+xn()"
    (\t1 t2 -> unsafeLookup (t1, t2) arithOpaPrecMatrix)
    [0, 1, 2, 3]
    [0]
    [1, 3]
    (\s  t  -> lookupOrDefault (s,  t)  arithOpaDeltaShift [])
    (\s  t  -> lookupOrDefault (s,  t)  arithOpaDeltaPush  [])
    (\s1 s2 -> lookupOrDefault (s1, s2) arithOpaDeltaPop   [])

tests :: TestTree
tests = testGroup "OPA tests"
  [ testCase "Arithmetic OPA run with \"(n+n)xn\"" $
      assertBool "Automaton does not accept" $ run arithOpa "(n+n)xn"
  ]

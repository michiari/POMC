{- |
   Module      : EvalFormulas
   Copyright   : 2021-23 Michele Chiari
   License     : MIT
   Maintainer  : Michele Chiari
-}

module EvalFormulas (TestCase, ap, zipExpected, excludeIndices, formulas) where

import Pomc.Potl (Formula(..), Dir(..), Prop(..))

type TestCase = (String, Formula String)

ap :: a -> Formula a
ap = Atomic . Prop

zipExpected :: [TestCase] -> [Bool] -> [(TestCase, Bool)]
zipExpected cases expected
  | length cases == length expected = zip cases expected
  | otherwise = error "TestCases and Expected values of different lengths!"

excludeIndices :: Ord a => [a] -> [Int] -> [a]
excludeIndices l is = fst $
  foldr (\x (xs, i) -> if i `notElem` is then (x:xs, i-1) else (xs, i-1)) ([], length l - 1) l

formulas :: [TestCase]
formulas =
  base_tests
  ++ chain_next
  ++ contains_exc
  ++ data_access
  ++ empty_frame
  ++ exception_safety
  ++ hier_down
  ++ hier_insp
  ++ hier_insp_exc
  ++ hier_up
  ++ normal_ret
  ++ no_throw
  ++ stack_inspection
  ++ uninstall_han
  ++ until_exc
  ++ until_misc

base_tests :: [TestCase]
base_tests =
  [ ( "0 - First Call"
    , ap "call"
    ),
    ( "1 - First Not Call"
    , Not . ap $ "call"
    ),
    ( "2 - Not Always call"
    , Not . Always . ap $ "call"
    ),
    ( "3 - Call and not call"
    , (ap "call" `And` (Not (ap "call")))
    ),
    ( "4 - Call and ret"
    , (ap "call" `And` ap "ret")
    ),
    ( "5 - Call, next ret 1"
    , ((ap "call") `And` (PNext Down (ap "ret")))
    ),
    ( "6 - Call, next ret 2"
    , (ap "call"
       `And` (PNext Down (ap "ret"))
       `And` (PNext Up (ap "ret")))
    ),
    ( "7 - Call, next down call"
    , (ap "call" `And` (PNext Down (ap "call")))
    ),
    ( "8 - Call, next up call"
    , (ap "call" `And` (PNext Up (ap "call")))
    ),
    ( "9 - Exc, back call pa"
    , (PNext Up ((ap $ "exc")
                 `And` (PBack Up (ap "call") `And` ap "pa")))
    ),
    ( "10 - Matched call 1"
    , (ap "call" `And` (XNext Down (ap "ret")))
    ),
    ( "11 - Matched call 2"
    , (ap "call" `And` (XNext Down (ap "ret")) `And` (XNext Up (ap "ret")))
    ),
    ( "12 - Impossible downward exc"
    , (ap "call" `And` (XNext Down (ap "exc")))
    ),
    ( "13 - Nested calls"
    , (ap "call" `And` (XNext Down (ap "call")))
    ),
    ( "14 - Inner call before exc"
    , (ap "call" `And` (XNext Up (ap "exc" `And` (XBack Up $ ap "call"))))
    ),
    ( "15 - No han until ret"
    , (ap "call" `And` Until Down (Not . ap $ "han") (ap "ret"))
    ),
    ( "16 - No han until down exc"
    , (ap "call" `And` Until Down (Not . ap $ "han") (ap "exc"))
    ),
    ( "17 - Next exp, not pa since pb"
    , (ap "call" `And` (XNext Up (ap "exc" `And` (PBack Up $ Since Up (Not . ap $ "pa") (ap "pb")))))
    ),
    ( "18 - Call exc and not pa until pb in between"
    , (ap "call"
        `And` (XNext Up (ap "exc"))
        `And` (PNext Down $ HUntil Down (Not . ap $ "pa") (ap "pb")))
    ),
    ( "19 - XNext Down HNext Up"
    , (ap "call" `And` (XNext Down (HNext Up $ ap "pa")))
    ),
    ( "20 - Call exc and pa in between"
    , (ap "call" `And` (XNext Up (ap "exc")) `And` (PNext Down $ HNext Down (ap "pa")))
    ),
    ( "21 - Nested calls HNext"
    , (ap "call"
       `And` (XNext Down (ap "ret"))
       `And` (XNext Down (HNext Up $ ap "pa")))
    ),
    ( "22 - Nested calls HUntil"
    , (ap "call"
       `And` (XNext Down (ap "ret"))
       `And` (XNext Down (HUntil Up (ap "pa") (ap "pb"))))
    ),
    ( "23 - XNext Down HNext Up perr"
    , (ap "call" `And` (XNext Down (HNext Up $ ap "perr")))
    )
  ]

chain_next :: [TestCase]
chain_next =
  [ ( "24 - First position has an inner call to perr"
    , XNext Down $ ap "perr"
    ),
    ( "25 - Third position is call terminated by an exception"
    , PNext Down $ PNext Down $ (ap "call") `And` (XNext Up $ ap "exc")
    ),
    ( "26 - Second position is a handler catching an exception that terminates more than one call"
    , PNext Down $ ap "han" `And` (XNext Down $ ap "exc" `And` XBack Up (ap "call"))
    ),
    ( "27 - Second position is a handler not catching an exception that terminates more than one call"
    , PNext Down $ ap "han" `And` (Not $ (XNext Down $ ap "exc" `And` XBack Up (ap "call")))
    ),
    ( "28 - All exceptions terminate more than one call"
    , Always $ ap "exc" `Implies` (XBack Up $ ap "call")
    )
  ]

contains_exc :: [TestCase]
contains_exc =
  [ ( "29 - First position is a call whose function frame contains \
      \at least one exc that does not terminate it."
    , Until Down T (ap "exc")
    ),
    ( "30 - Third position is a call whose function frame contains \
      \at least one exc that does not terminate it."
    , PNext Down $ PNext Down $ Until Down T (ap "exc")
    ),
    ( "31 - First position is a call whose function frame does not contain excs."
    , Not $ Until Down T (ap "exc")
    ),
    ( "32 - No function currently in the stack is terminated by an exception."
    , Not $ Until Up T (ap "exc")
    )
  ]

data_access :: [TestCase]
data_access =
  [ ( "33 - If a procedure pa or its subprocedures write to a variable x, \
      \then they are terminated by an exception."
    , Always $ (ap "call" `And` ap "pa" `And` Until Down (Not $ ap "ret") (ap "WRx"))
      `Implies` XNext Up (ap "exc")
    )
  ]

empty_frame :: [TestCase]
empty_frame =
  [ ( "34 - Second position terminates an empty function frame"
    , PNext Down $ PBack Up $ ap "call"
    ),
    ( "35 - Fourth position terminates an empty function frame"
    , PNext Down $ PNext Down $ PNext Down $ PBack Up $ ap "call"
    ),
    ( "36 - First position contains an inner call with empty body"
    , XNext Down $ PNext Down $ PBack Up $ ap "call"
    ),
    ( "37 - First position does not contain an inner call with empty body"
    , Not $ XNext Down $ PNext Down $ PBack Up $ ap "call"
    )
  ]

exception_safety :: [TestCase]
exception_safety =
  [ ( "38 - If a call to procedure `pa' is terminated by an exception, \
      \`eb' holds in that exception."
    , Always $ (ap "call" `And` ap "pa" `And` (PNext Up (ap "exc") `Or` XNext Up (ap "exc")))
      `Implies` ((PNext Up $ ap "eb") `Or` (XNext Up $ ap "eb"))
    )
  ]

hier_down :: [TestCase]
hier_down =
  [ ( "39 - A call is terminated by an exception, and the next function \
      \terminated by the same exception is pb"
    , Eventually $ HNext Down (ap "pb")
    ),
    ( "40 - A call is terminated by an exception, and the previous function \
      \terminated by the same exception is pb"
    , Eventually $ HBack Down (ap "pb")
    ),
    ( "41 - A call to procedure pa is terminated by an exception, \
      \and the same exception later terminates pc"
    , Eventually $ ap "pa" `And` HUntil Down (ap "call") (ap "pc")
    ),
    ( "42 - A call to procedure pc is terminated by an exception, \
      \and the same exception earlier terminated pa"
    , Eventually $ ap "pc" `And` HSince Down (ap "call") (ap "pa")
    )
  ]

hier_insp :: [TestCase]
hier_insp =
  [ ( "43 - If procedure pb is called by a function, \
      \the same function must later call perr after pb returns, \
      \without calling pc in the meantime."
    , Always $ (ap "call" `And` ap "pb") `Implies` (HUntil Up (Not . ap $ "pc") (ap "perr"))
    )
  ]

hier_insp_exc :: [TestCase]
hier_insp_exc =
  [ ( "44 - If an instance of function pc is terminated by an uncaught exception, \
      \then function pb must be present in the backtrace, and it is also terminated. \
      \Also, the same exception cannot terminate pa before pb."
    , Always $ (ap "pc" `And` XNext Up (ap "exc")) `Implies` (HSince Down (Not . ap $ "pa") (ap "pb"))
    )
  ]

hier_up :: [TestCase]
hier_up =
  [ ( "45 - There is a call to a function such that the next function called by its parent is perr."
    , Eventually $ HNext Up (ap "perr")
    ),
    ( "46 - There is a call to a function such that the previous function called \
      \by its parent is perr."
    , Eventually $ HBack Up (ap "perr")
    ),
    ( "47 - There is a call to function pa such that its parent later calls pb."
    , Eventually $ ap "pa" `And` HUntil Up (ap "call") (ap "pb")
    ),
    ( "48 - There is a call to function pb such that its parent previously called pa."
    , Eventually $ ap "pb" `And` HSince Up (ap "call") (ap "pa")
    )
  ]

normal_ret :: [TestCase]
normal_ret =
  [ ( "49 - All calls have a matched return"
    , Always $ ap "call" `Implies` XNext Down (ap "ret")
    ),
    ( "50 - No call is terminated by an exception"
    , Always $ ap "call" `Implies` (Not $ PNext Up (ap "exc"))
    )
  ]

no_throw :: [TestCase]
no_throw =
  [ ( "51 - Procedure pa can never be terminated by an exception"
    , Always $ (ap "call" `And` ap "pa") `Implies`
      (Not $ PNext Up (ap "exc") `Or` XNext Up (ap "exc"))
    ),
    ( "52 - Procedure pa can never be terminated by an exception"
    , Always $ ap "exc" `Implies`
      (Not $ PBack Up (ap "call" `And` ap "pa") `Or` XBack Up (ap "call" `And` ap "pa"))
    )
  ]

stack_inspection :: [TestCase]
stack_inspection =
  [ ( "53 - If procedure `pa' is present into the stack when \
      \procedure `pb' is called, `pb' throws an exception."
    , Always $ (ap "call" `And` ap "pb" `And` (Since Down T (ap "call" `And` ap "pa")))
      `Implies` (PNext Up (ap "exc") `Or` XNext Up (ap "exc"))
    ),
    ( "54 - If procedure `pa' is present into the stack when \
      \procedure `pb' is called, `pb' or one of the functions it calls throw an exception."
    , Always $ (ap "call" `And` ap "pb" `And` (Since Down T (ap "call" `And` ap "pa")))
      `Implies` (Until Down T (PNext Up (ap "exc") `Or` XNext Up (ap "exc")))
    )
  ]

uninstall_han :: [TestCase]
uninstall_han =
  [ ( "55 - All exception handlers are uninstalled by a return \
      \statement (i.e., they do not catch any exception)"
    , Always $ ap "han" `Implies` XNext Up (ap "ret")
    )
  ]

until_exc :: [TestCase]
until_exc =
  [ ( "56 - The first position is inside a function call terminated by an exception, \
      \or a handler that catches an exception."
    , Until Up T (ap "exc")
    ),
    ( "57 - The third position is inside a function call terminated by an exception, \
      \or a handler that catches an exception."
    , PNext Down $ PNext Down $ Until Up T (ap "exc")
    ),
    ( "58 - The third position is inside a function call terminated by an exception, \
      \or a handler that catches an exception or pc is called indefinitely."
    , PNext Down $ PNext Down $
      (Until Up T (ap "exc")) `Or` (PNext Down $ Always $ ap "call" `And` ap "pc")
    ),
    ( "59 - Each call to pc is enclosed into a handler-caught exception pair."
    , Always $ (ap "call" `And` ap "pc") `Implies`
      (Until Up T $ ap "exc" `And` (XBack Down $ ap "han"))
    )
  ]

until_misc :: [TestCase]
until_misc =
  [ ( "60 - The call in the first position makes at least a direct subcall to function perr, \
      \which returns normally."
    , Until Down (ap "call") (ap "ret" `And` ap "perr")
    ),
    ( "61 - The call in the first position makes a function call, \
      \and before that, there is an instance of function pb (even in a previous inner call)."
    , XNext Down $ ap "call" `And` (Since Up (ap "call" `Or` ap "exc") (ap "pb"))
    ),
    ( "62 - From the third position, it is possible to reach a return, possibly of another function."
    , PNext Down $ PNext Down $ Until Up (ap "call" `Or` ap "exc") (ap "ret")
    )
  ]

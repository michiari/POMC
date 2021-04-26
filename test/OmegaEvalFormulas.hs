module OmegaEvalFormulas (omegaFormulas) where

import Pomc.PotlV2 (Formula(..), Dir(..), Prop(..))

type TestCase = (String, Formula String, [String], Bool)

ap :: a -> Formula a
ap = Atomic . Prop

omegaFormulas :: [TestCase]
omegaFormulas = chain_next
  ++ contains_exc
  -- ++ data_access
  ++ empty_frame
  -- ++ exception_safety
  ++ hier_down
  ++ hier_insp
  -- ++ hier_insp_exc
  ++ hier_up
  ++ normal_ret
  ++ no_throw
  ++ stack_inspection
  ++ uninstall_han
  ++ until_exc
  ++ until_misc
  

chain_next :: [TestCase]
chain_next =
  [ ( "First position has an inner call to perr"
    , XNext Down $ ap "perr"
    , ["pa", "pb", "pc", "perr"]
    , True
    ),
    ( "Third position is call terminated by an exception"
    , PNext Down $ PNext Down $ (ap "call") `And` (XNext Up $ ap "exc")
    , ["pa", "pb", "pc", "perr"]
    , True
    ),
    ( "Second position is a handler catching an exception that terminates more than one call"
    , PNext Down $ ap "han" `And` (XNext Down $ ap "exc" `And` XBack Up (ap "call"))
    , ["pa", "pb", "pc", "perr"]
    , True
    ),
    ( "Second position is a handler not catching an exception that terminates more than one call"
    , PNext Down $ ap "han" `And` (Not $ (XNext Down $ ap "exc" `And` XBack Up (ap "call")))
    , ["pa", "pb", "pc", "perr"]
    , True -- added
    ),
    ( "All exceptions terminate more than one call"
    , Always $ ap "exc" `Implies` (XBack Up $ ap "call")
    , ["pa", "pb", "pc", "perr"]
    , True
    )
    ]

contains_exc :: [TestCase]
contains_exc =
  [ ( "First position is a call whose function frame contains excs, \
      \but which is not directly terminated by one of them."
    , Until Down T (ap "exc")
    , ["pa", "pb", "pc", "perr"]
    , True
    ),
    ( "Third position is a call whose function frame contains excs, \
      \but which is not directly terminated by one of them."
    , PNext Down $ PNext Down $ Until Down T (ap "exc")
    , ["pa", "pb", "pc", "perr"]
    , True
    ), 
    ( "First position is a call whose function frame does not contain excs \
       \which do not directly terminate the call."
    , Not $ Until Down T (ap "exc")
    , ["pa", "pb", "pc", "perr"]
    , True -- added
    ),
    ( "First position is a call whose function frame does not contain excs \
      \which directly terminate the call."
    , Not $ Until Up T (ap "exc")
    , ["pa", "pb", "pc", "perr"]
    , True -- added
    )

  ]

data_access :: [TestCase]
data_access =
  [ ( "If a procedure pa or its subprocedures write to a variable x, \
      \then they are terminated by an exception."
    , Always $ (ap "call" `And` ap "pa" `And` Until Down (Not $ ap "ret") (ap "WRx"))
      `Implies` XNext Up (ap "exc")
    , ["pa", "pb", "pc", "WRx"]
    , True
    )
  ]

empty_frame :: [TestCase]
empty_frame =
  [ ( "Second position terminates an empty function frame"
    , PNext Down $ PBack Up $ ap "call"
    , ["pa", "pb", "pc", "perr"]
    , True
    ),
    ( "Fourth position terminates an empty function frame"
    , PNext Down $ PNext Down $ PNext Down $ PBack Up $ ap "call"
    , ["pa", "pb", "pc", "perr"]
    , True
    ),
    ( "First position does not contain an inner call with empty body"
    , Not $ XNext Down $ PNext Down $ PBack Up $ ap "call"
    , ["pa", "pb", "pc", "perr"]
    , True
    )
  ]

exception_safety :: [TestCase]
exception_safety =
  [ ( "If a call to procedure `pa' is terminated by an exception, \
      \`eb' holds in that exception."
    , Always $ (ap "call" `And` ap "pa" `And` (PNext Up (ap "exc") `Or` XNext Up (ap "exc")))
      `Implies` ((PNext Up $ ap "eb") `Or` (XNext Up $ ap "eb"))
    , ["pa", "eb"]
    , True
    )
  ]

hier_down :: [TestCase]
hier_down =
  [ ( "A call is terminated by an exception, and the next function \
      \terminated by the same exception is pb"
    , (Eventually $ HNext Down (ap "pb")) 
    , ["pa", "pb", "pc"]
    , True
    ),
    ( "A call is terminated by an exception, and the previous function \
      \terminated by the same exception is pb"
    , Eventually $ HBack Down (ap "pb")
    , ["pa", "pb", "pc"]
    , True
    ),
    ( "A call to procedure pa is terminated by an exception, \
      \and the same exception later terminates pc"
    , Eventually $ ap "pa" `And` HUntil Down (ap "call") (ap "pc")
    , ["pa", "pb", "pc"]
    , True
    ),
    ( "A call to procedure pc is terminated by an exception, \
      \and the same exception earlier terminated pa"
    , Eventually $ ap "pc" `And` HSince Down (ap "call") (ap "pa")
    , ["pa", "pb", "pc"]
    , True
    )
  ]

hier_insp_exc :: [TestCase]
hier_insp_exc =
  [ ( "If an instance of function pc is terminated by an uncaught exception, \
      \then function pb must be present in the backtrace, and it is also terminated. \
      \Also, the same exception cannot terminate pa before pb."
    , Always $ (ap "pc" `And` XNext Up (ap "exc")) `Implies` (HSince Down (Not . ap $ "pa") (ap "pb"))
    , ["pa", "pb", "pc"]
    , True
    )
  ]

hier_insp :: [TestCase]
hier_insp =
  [ ( "If procedure pb is called by a function, \
      \the same function must later call perr after pb returns, \
      \without calling pc in the meantime."
    , Always $ (ap "call" `And` ap "pb") `Implies` (HUntil Up (Not . ap $ "pc") (ap "perr"))
    , ["pb", "pc", "perr"]
    , True
    )
  ]

hier_up :: [TestCase]
hier_up =
  [ ( "There is a call to a function such that the next function called by its parent is perr."
    , Eventually $ HNext Up (ap "perr")
    , ["pa", "pb", "perr"]
    , True
    ),
    ( "There is a call to a function such that the previous function called by its parent is perr."
    , Eventually $ HBack Up (ap "perr")
    , ["pa", "pb", "perr"]
    , True
    ),
    ( "There is a call to function pa such that its parent later calls pb."
    , Eventually $ ap "pa" `And` HUntil Up (ap "call") (ap "pb")
    , ["pa", "pb", "perr"]
    , True
    ),
    ( "There is a call to function pb such that its parent previously called pa."
    , Eventually $ ap "pb" `And` HSince Up (ap "call") (ap "pa")
    , ["pa", "pb", "perr"]
    , True
    )
  ]

normal_ret :: [TestCase]
normal_ret =
  [ ( "All calls have a matched return"
    , Always $ (ap "call") `Implies` XNext Down (ap "ret")
    , ["e1"]
    , True
    ),
    ( "No call is terminated by an exception"
    , Always $ ap "call" `Implies` (Not $ PNext Up (ap "exc"))
    , ["e1"]
    , True
    )
  ]

no_throw :: [TestCase]
no_throw =
  [ ( "Procedure pa can never be terminated by an exception"
    , Always $ (ap "call" `And` ap "pa") `Implies`
      (Not $ PNext Up (ap "exc") `Or` XNext Up (ap "exc"))
    , ["pa", "pb", "pc"]
    , True
    ),
    ( "Procedure pa can never be terminated by an exception"
    , Always $ ap "exc" `Implies`
      (Not $ PBack Up (ap "call" `And` ap "pa") `Or` XBack Up (ap "call" `And` ap "pa"))
    , ["pa", "pb", "pc"]
    , True
    )
  ]

stack_inspection :: [TestCase]
stack_inspection =
  [ ( "If procedure `pa' is present into the stack when \
      \procedure `pb' is called, `pb' throws an exception."
    , Always $ (ap "call" `And` ap "pb" `And` (Since Down T (ap "call" `And` ap "pa")))
      `Implies` (PNext Up (ap "exc") `Or` XNext Up (ap "exc"))
    , ["pa", "pb"]
    , True
    ), -- modified
    ( "If procedure `pa' is present into the stack when \
      \procedure `pb' is called, `pb' or one of the functions it calls throw an exception."
    , Always $ (ap "call" `And` ap "pb" `And` (Since Down T (ap "call" `And` ap "pa")))
      `Implies` (Until Down T (PNext Up (ap "exc") `Or` XNext Up (ap "exc")))
    , ["pa", "pb"]
    , True
    ) -- modified
  ]

uninstall_han :: [TestCase]
uninstall_han =
  [ ( "All exception handlers are uninstalled by a return \
      \statement (i.e., they do not catch any exception)"
    , Always $ ap "han" `Implies` XNext Up (ap "ret")
    , ["pa", "pb", "pc"]
    , True
    )
  ]

until_exc :: [TestCase]
until_exc =
  [ ( "The first position is inside a function call terminated by an exception, \
      \or a handler that catches an exception."
    , Until Up T (ap "exc")
    , ["pa", "pb", "pc", "perr"]
    , True
    ),
    ( "The third position is inside a function call terminated by an exception, \
      \or a handler that catches an exception."
    , PNext Down $ PNext Down $ Until Up T (ap "exc")
    , ["pa", "pb", "pc", "perr"]
    , True
    ){-,
    ( "The third position is inside a function call terminated by an exception, \
      \or a handler that catches an exception or pc is called indefinitely."
    , PNext Down $ PNext Down $ (Until Up T (ap "exc")) `Or` (PNext Down $ Always $ ap "call" `And` ap "pc")
    , ["pa", "pb", "pc", "perr"]
    , True
    )-}, --added
    ( "Each call to pc is enclosed into a handler-caught exception pair."
    , Always $ (ap "call" `And` ap "pc") `Implies`
      (Until Up T $ ap "exc" `And` (XBack Down $ ap "han"))
    , ["pa", "pb", "pc", "perr"]
    , True
    )
  ]

until_misc :: [TestCase]
until_misc =
  [ ( "The call in the first position makes at least a direct subcall to function perr, \
      \which returns normally."
    , Until Down (ap "call") (ap "ret" `And` ap "perr")
    , ["pa", "pb", "pc", "perr"]
    , True
    ),
    ( "The call in the first position makes a function call, \
      \and before that, there is an instance of function pb (even in a previous inner call)."
    , XNext Down $ ap "call" `And` (Since Up (ap "call" `Or` ap "exc") (ap "pb"))
    , ["pa", "pb", "pc", "perr"]
    , True
    ),
    ( "From the third position, it is possible to reach a return, possibly of another function."
    , PNext Down $ PNext Down $ Until Up (ap "call" `Or` ap "ret") (ap "ret")
    , ["pa", "pb", "pc", "perr"]
    , True
    )
  ]
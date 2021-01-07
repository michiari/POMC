( "Accepting HSince Up"
        , True
        , formulaAt 6 $ HSince Up (Atomic . Prop $ "t") (Atomic . Prop $ "tbeg")
        , stlPrecRelV1
        , map (S.fromList . map Prop) (stlAnnotateV1 ["han", "call", "tbeg", "t", "t", "t", "ret"])
        )
      , ( "Rejecting Not HSince Up"
        , False
        , formulaAt 6 $ Not ( HSince Up (Atomic . Prop $ "t") (Atomic . Prop $ "tbeg"))
        , stlPrecRelV1
        , map (S.fromList . map Prop) (stlAnnotateV1 ["han", "call", "tbeg", "t", "t", "t", "ret"])
        )
      , ( "Rejecting HSince Up"
        , False
        , formulaAt 6 $ HSince Up (Not . Atomic . Prop $ "texc") (Atomic . Prop $ "tbeg")
        , stlPrecRelV1
        , map (S.fromList . map Prop) (stlAnnotateV1 ["han", "call", "tbeg", "t", "texc", "t", "ret"])
        )
      , 




----------------------------------------------------------------------------------------------------------------------------


( "Accepting predicate on first word position"
        , True
        , Atomic . Prop  $ "call"
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "ret"]
        )
      , ( "Rejecting Not predicate on first word position"
        , False
        , Not (Atomic . Prop  $ "call")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "ret"]
        )
      , ( "Accepting Not"
        , True
        , Not . Atomic . Prop  $ "ret"
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "ret"]
        )
      , ( "Rejecting Not Not"
        , False
        , Not . Not . Atomic . Prop  $ "ret"
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "ret"]
        )
      , ( "Rejecting Not"
        , False
        , Not . Atomic . Prop  $ "call"
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "ret"]
        )
      , ( "Accepting multiple negation"
        , True
        , Not . Not . Not . Not . Atomic . Prop  $ "call"
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "ret"]
        )
      , ( "Rejecting multiple negation"
        , False
        , Not . Not . Not . Not . Not . Atomic . Prop  $ "call"
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "ret"]
        )
      , ( "Accepting And"
        , True
        , And (Atomic $ Prop "call") (Not $ Atomic $ Prop "ret")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "ret"]
        )
      , ( "Rejecting Not And"
        , False
        , Not (And (Atomic $ Prop "call") (Not $ Atomic $ Prop "ret"))
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "ret"]
        )
      , ( "Accepting Or"
        , True
        , Or (Atomic . Prop $ "call") (Atomic . Prop $ "ret")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "ret"]
        )
      , ( "Rejecting Not Or"
        , False
        , Not (Or (Atomic . Prop $ "call") (Atomic . Prop $ "ret"))
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "ret"]
        )
      , ( "Accepting PNext Up"
        , True
        , PNext Up (Atomic $ Prop "ret") 
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "ret"]
        )
      , ( "Rejecting Not PNext Up"
        , False
        , Not $ PNext Up (Atomic $ Prop "ret") 
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "ret"]
        )
      , ( "Rejecting PNext Up"
        , False
        , PNext Up (Atomic $ Prop "call") 
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "ret"]
        )
      , ( "Accepting PNext Down"
        , True
        , PNext Down (Atomic $ Prop "ret") 
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "ret"]
        )
      , ( "Rejecting Not PNext Down"
        , False
        , Not $ PNext Down (Atomic $ Prop "ret")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "ret"]
        )
      , ( "Rejecting PNext Down"
        , False
        , PNext Down (Atomic $ Prop "call") 
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "ret"]
        )
      , ( "Rejecting OOB PNext [Up]"
        , False
        , PNext Up (PNext Up (Atomic $ Prop "call")) 
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "ret"]
        )
      ,  ( "Rejecting OOB PNext [Down]"
        , False
        , PNext Down (PNext Up (Atomic $ Prop "call")) 
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "ret"]
        )
      , ( "Accepting PBack Up [Up]"
        , True
        , PNext Up (PBack Up (Atomic $ Prop "call"))
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "ret"]
        )
      , ( "Accepting PBack Up [Down]"
        , True
        , PNext Down (PBack Up (Atomic $ Prop "call"))
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "ret"]
        )
      , ( "Accepting PBack Down [Up]"
        , True
        , PNext Up (PBack Down (Atomic $ Prop "call"))
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "ret"]
        )
      , ( "Accepting PBack Down [Down]"
        , True
        , PNext Down (PBack Down (Atomic $ Prop "call"))
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "ret"]
        )
      , ( "Rejecting Not PBack Up [Up]"
        , False
        , PNext Up $ Not (PBack Up (Atomic $ Prop "call"))
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "ret"]
        )
      , ( "Rejecting Not PBack Up [Down]"
        , False
        , PNext Down $ Not (PBack Up (Atomic $ Prop "call"))
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "ret"]
        )
      , ( "Rejecting Not PBack Down [Up]"
        , False
        , PNext Up $ Not (PBack Down (Atomic $ Prop "call"))
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "ret"]
        )
      , ( "Rejecting Not PBack Down [Down]"
        , False
        , PNext Down $ Not (PBack Down (Atomic $ Prop "call"))
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "ret"]
        )
      , ( "Rejecting OOB PBack Up"
        , False
        , PBack Up (Atomic $ Prop "call")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "ret"]
        )
      , ( "Rejecting OOB PBack Down"
        , False
        , PBack Down (Atomic $ Prop "call")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "ret"]
        )
      , ( "Rejecting OOB PBack Up [Up]"
        , False
        , PBack Up $ PBack Up (Atomic $ Prop "call")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "ret"]
        )
      , ( "Rejecting OOB PBack Up [Down]"
        , False
        , PBack Down $ PBack Up (Atomic $ Prop "call")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "ret"]
        )
      , ( "Rejecting OOB PBack Down [Up]"
        , False
        , PBack Up $ PBack Down (Atomic $ Prop "call")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "ret"]
        )
      , ( "Rejecting OOB PBack Down [Down]"
        , False
        , PBack Down $ PBack Down (Atomic $ Prop "call")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "ret"]
        )
      , ( "Accepting XNext Down" 
        , True
        , XNext Down (Atomic $ Prop "thr")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["han", "call", "thr"]
        )
      , ( "Rejecting Not XNext Down"
        , False
        , Not $ XNext Down (Atomic $ Prop "thr")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["han", "call", "thr"]
        )
      , ( "Rejecting XNext Down"
        , False
        , XNext Down (Atomic $ Prop "ret")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "call", "thr"]
        )
      , ( "Accepting inner XNext Down"
        , True
        ,  PNext Down $ XNext Down (Atomic $ Prop "thr")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "han", "call", "thr", "ret"]
        )
      , ( "Rejecting inner XNext Down"
        , False
        , PNext Down $ XNext Down (Atomic $ Prop "ret")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "han", "call", "thr", "ret"]
        )
      , ( "Push after pop with XNext Down in closure"
        , True
        , Or (XNext Down (Atomic $ Prop "call")) (Atomic $ Prop "call") -- here (Atomic $ Prop "call") holds, this is checked in the next test
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "ret", "call", "ret"]
        )
      , ( "Check first element"
        , True
        , (Atomic $ Prop "call") 
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "ret", "call", "ret"]
        )
      ,( "Accepting XNext Up"
        , True
        , XNext Up (Atomic $ Prop "ret")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["han", "thr", "ret"]
        )
      , ( "Rejecting Not XNext Up" 
        , False
        , Not $ XNext Up (Atomic $ Prop "ret")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["han", "thr", "ret"]
        )
      , ( "Accepting inner XNext Up"
        , True
        , PNext Down $ XNext Up (Atomic $ Prop "ret")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "han", "thr", "ret"]
        )
      , ( "Rejecting inner XNext Up" 
        , False
        , PNext Up $ XNext Up (Atomic $ Prop "ret")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "call", "thr", "han", "ret"]
        )
      , ( "Accepting XNext Down through Equal relation"  
        , True
        , XNext Down (Atomic $ Prop "ret")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "han", "ret"]
        )
      , ( "Accepting XNext Up through Equal relation" 
        , True
        , XNext Up (Atomic $ Prop "ret")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "han", "ret"]
        )
      , ( "Accepting XNext Down through Yield relation" 
        , True
        , XNext Down(Atomic $ Prop "thr")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["han", "call", "thr"]
        )
      , ( "Accepting XNext Up through Take relation" 
        , True
        , XNext Up (Atomic $ Prop "ret")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["han", "thr", "ret"]
        )
      , ( "Rejecting Not XNext Down through Equal relation" 
        , False
        , Not $ XNext Down (Atomic $ Prop "ret")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "han", "ret"] 
        )
      , ( "Rejecting Not XNext Up through Equal relation"
        , False
        , Not $ XNext Up (Atomic $ Prop "ret")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "han", "ret"] 
        )
      , ( "Rejecting Not XNext Down through Yield relation" 
        , False
        , Not $ XNext Down (Atomic $ Prop "thr")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["han", "call", "thr"]
        )
      , ( "Rejecting Not XNext Up through Take relation" 
        , False
        , Not $ XNext Up (Atomic $ Prop "ret")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["han", "thr", "ret"]
        )
      , ( "Rejecting Not Or of XNext formulas through Take relation" 
        , False
        , Not $ (Or (XNext Up (Atomic $ Prop "ret")) (Or (XNext Up (Atomic $ Prop "ret")) (XNext Down (Atomic $ Prop "ret"))))
        , stlPrecRelV1
        , map (S.singleton . Prop) ["han", "thr", "ret"]
        )
      , ( "Rejecting XNext Down due to no inner chain"
        , False
        , XNext Down (Atomic $ Prop "ret")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "ret"] -- there is no inner chain ;)
        )
      , ( "Rejecting XNext Up due to no inner chain"
        , False
        , XNext Up (Atomic $ Prop "ret")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "ret"] -- there is no inner chain ;)
        )
      , ( "Rejecting XNext Up" 
        , False
        , XNext Up (Atomic $ Prop "ret")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["han", "call", "thr"]
        )
      , ( "Rejecting XNext Down"
        , False
        , XNext Down (Atomic $ Prop "ret")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["han", "thr", "ret"]
        )
        ------------ Until operators --------------------------------
      , ( "Accepting Until Down through XNext with Yield relation" 
        , True
        , Until Down (Not . Atomic . Prop $ "call") (Atomic $ Prop "thr")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["han", "call", "thr"]
        )
      , ( "Rejecting Until Down"
        , False
        , Until Down (Not . Atomic . Prop $ "han") (Atomic $ Prop "thr")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["han", "call", "thr"]
        )
      , ( "Accepting Until Down through XNext with Equal relation"
        , True
        , Until Down (Not . Atomic . Prop $ "han") (Atomic $ Prop "ret")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "han", "ret"]
        )
      , ( "Accepting Until Up through XNext with Equal relation"
        , True
        , Until Up (Not . Atomic . Prop $ "han") (Atomic $ Prop "ret")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "han", "ret"]
        )
      , ( "Accepting Until Up through XNext with Take relation"
        , True
        , Until Up (Not . Atomic . Prop $ "thr") (Atomic $ Prop "ret")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["han", "thr", "ret"]
        )
      , ( "Rejecting Until Up"
        , False
        , Until Up (Not . Atomic . Prop $ "han") (Atomic $ Prop "ret")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["han", "thr", "ret"]
        )
      , ( "Accepting Until Down - XOR check" -- this fails if the Until conditions for an atom
        , True                         -- are implemented with XOR instead of OR
        , Until Down (Not . Atomic . Prop $ "thr") (Atomic $ Prop "ret")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "han", "thr", "ret"]
        )
      , ( "Rejecting Not Until Down - XOR check"
        , False
        , Not (Until Down (Not . Atomic . Prop $ "thr") (Atomic $ Prop "ret"))
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "han", "thr", "ret"]
        )
      , ( "Accepting Until Up - XOR check" -- this fails if the Until conditions for an atom
        , True                         -- are implemented with XOR instead of OR
        , Until Up (Not . Atomic . Prop $ "thr") (Atomic $ Prop "ret")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "han", "thr", "ret"]
        )
      , ( "Rejecting Not Until Up - XOR check"
        , False
        , Not (Until Up (Not . Atomic . Prop $ "thr") (Atomic $ Prop "ret"))
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "han", "thr", "ret"]
        )
      ---------------------- XBack operator -------------------------------------------------------------------------
      ,





----------------------------------------------------------------------------------------------------------------------------------------
---------------------------------------------------------------------------------------------------------------------------------------


        , ( "Rejecting inner XBack Up"
        , False
        , formulaAfter [Down, Down, Down] $ XBack Up (Atomic $ Prop "call")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "call", "han", "thr", "ret", "ret"]
        )
      , ( "Rejecting inner XBack Up -- v2"  
        , False
        , formulaAfter [Down, Up, Up] $ XBack Up (Atomic $ Prop "han")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["han", "call", "thr", "thr", "ret"]
        )
      , ( "Accepting XBack Up through the Equal relation" 
        , True
        , formulaAfter [Down, Up] $ XBack Up (Atomic $ Prop "call")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "han", "ret"]
        )
      , ( "Rejecting Not XBack Up through the Equal relation" 
        , False
        , formulaAfter [Down, Up] $ Not (XBack Up (Atomic $ Prop "call"))
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "han", "ret"]
        )
      , ( "Accepting inner XBack Up through Equal relation" 
        , True
        , formulaAfter [Down, Down, Up] $ XBack Up (Atomic $ Prop "call")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "call", "han", "ret", "ret"]
        )
      , ( "Accepting XBack Up through inner XBack Down" 
        , True
        , formulaAfter [Down, Up, Up , Up] $ XBack Up (Atomic $ Prop "han")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["han", "call", "thr", "thr", "ret"]
        )
      , ( "Rejecting XBack Up with inner XBack Down"
        , False
        , formulaAfter [Down, Up , Up, Up] $ XBack Up (Atomic $ Prop "call")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["han", "call", "thr", "thr", "ret"]
        )
      , ( "Accepting XBack Up through union of Yield and Take checksets"
        , True
        , formulaAfter [Down, Down, Up] $ XBack Up (Atomic $ Prop "call")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "call", "call", "thr"]
        )
       ------------ Since operator ---------------------------------------------------------
      , ( "Accepting Since Down through Yield relation"
        , True
        , formulaAfter [Down, Up] $ Since Down (Not . Atomic . Prop $ "call") (Atomic . Prop $ "han")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["han", "call", "thr"]
        )
      , ( "Rejecting Not Since Down through Yield relation"
        , False
        , formulaAfter [Down, Up] $ Not $ Since Down (Not . Atomic . Prop $ "call") (Atomic . Prop $ "han")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["han", "call", "thr"]
        )
      , ( "Rejecting Since Down through Yield relation"
        , False
        , formulaAfter [Down, Up] $ Since Down (Not . Atomic . Prop $ "thr") (Atomic . Prop $ "han")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["han", "call", "thr"]
        )
      , ( "Accepting Since Down through Equal relation"
        , True
        , formulaAfter [Down, Up] $ Since Down (Not . Atomic . Prop $ "han") (Atomic . Prop $ "call")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "han", "ret"]
        )
      , ( "Rejecting Since Down through Equal relation" 
        , False
        , formulaAfter [Down, Up] $ Since Down (Not . Atomic . Prop $ "ret") (Atomic . Prop $ "call")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "han", "ret"]
        )
      , ( "Accepting Since Up through Take relation"
        , True
        , formulaAfter [Down, Up] $ Since Up (Not . Atomic . Prop $ "thr") (Atomic . Prop $ "han")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["han", "thr", "ret"]
        )
      , ( "Rejecting Not Since Up through Take relation"
        , False
        , formulaAfter [Down, Up] $ Not $ Since Up (Not . Atomic . Prop $ "thr") (Atomic . Prop $ "han")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["han", "thr", "ret"]
        )
      , ( "Rejecting Since Up through Take relation"
        , False
        , formulaAfter [Down, Up] $ Since Up (Not . Atomic . Prop $ "ret") (Atomic . Prop $ "han")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["han", "thr", "ret"]
        )
      , ( "Accepting Since Up through Equal relation"
        , True
        , formulaAfter [Down, Up] $ Since Up (Not . Atomic . Prop $ "han") (Atomic . Prop $ "call")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "han", "ret"]
        )
      , ( "Rejecting Since Up through Equal relation" 
        , False
        , formulaAfter [Down, Up] $ Since Up (Not . Atomic . Prop $ "ret") (Atomic . Prop $ "call")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "han", "ret"]
        )
      --------------------- HNext and HBack operators --------------------------------------
      , ( "Accepting HNext Up"
        , True
        , formulaAfter [Down, Up] $ HNext Up (Atomic . Prop $ "thr")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["han", "call", "thr", "thr", "ret"]
        )
      , ( "Rejecting Not HNext Up"
        , False
        , formulaAfter [Down, Up] $ Not (HNext Up (Atomic . Prop $ "thr"))
        , stlPrecRelV1
        , map (S.singleton . Prop) ["han", "call", "thr", "thr", "ret"]
        )
      , ( "Rejecting HNext Up"
        , False
        , formulaAfter [Down, Up] $ HNext Up (Atomic . Prop $ "ret")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["han", "call", "thr", "ret"]
        )
      , ( "Accepting HBack Up"
        , True
        , formulaAfter [Down, Up ,Up] $ HBack Up (Atomic . Prop $ "thr")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["han", "call", "thr", "thr", "ret"]
        )
      , ( "Rejecting Not HBack Up"
        , False
        , formulaAfter [Down, Up, Up] $ Not (HBack Up (Atomic . Prop $ "thr"))
        , stlPrecRelV1
        , map (S.singleton . Prop) ["han", "call", "thr", "thr", "ret"]
        )
      , ( "Rejecting HBack Up"
        , False
        , formulaAfter [Down, Up] $ HBack Up (Atomic . Prop $ "call")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["han", "call", "thr", "ret"]
        )
      , ( "Accepting HNext Down"
        , True
        , HNext Down (Atomic . Prop $ "call")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "call", "call", "thr"]
        )
      , ( "Rejecting Not HNext Down"
        , False
        , Not (HNext Down (Atomic . Prop $ "call"))
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "call", "call", "thr"]
        )
      , ( "Rejecting HNext Down"
        , False
        , formulaAfter [Down] $ HNext Down (Atomic . Prop $ "call")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "call", "call", "thr"]
        )
      , ( "Accepting HBack Down"
        , True
        , formulaAfter [Down] $ HBack Down (Atomic . Prop $ "call")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "call", "call", "thr"]
        )
      , ( "Rejecting Not HBack Down"
        , False
        , formulaAfter [Down] $ Not (HBack Down (Atomic . Prop $ "call"))
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "call", "call", "thr"]
        )
      , ( "Rejecting HBack Down"
        , False
        , formulaAfter [Down, Down] $ HBack Down (Atomic . Prop $ "call")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "call", "call", "thr"]
        )
      , ( "Rejecting HBack Down -- v2"
        , False
        , HBack Down (Atomic . Prop $ "call")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "call", "call", "thr"]
        )
      , ( "Accepting T"
        , True
        , T
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "han", "thr", "ret"]
        )
      , ( "Rejecting Not T"
        , False
        , Not T
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "han", "thr", "ret"]
        )
      -------------- HUntil and HSince operators ---------------------------------------------
      , ( "Accepting HUntil Up"
        , True
        , formulaAt 3 $ HUntil Up (Atomic . Prop $ "t") (Atomic . Prop $ "tend")
        , stlPrecRelV1
        , map (S.fromList . map Prop) (stlAnnotateV1 ["han", "call", "t", "t", "t", "tend", "ret"])
        )
      , ( "Rejecting Not HUntil Up"
        , False
        , formulaAt 3 $ Not ( HUntil Up (Atomic . Prop $ "t")  (Atomic . Prop $ "tend"))
        , stlPrecRelV1
        , map (S.fromList . map Prop) (stlAnnotateV1 ["han", "call", "t", "t", "t", "tend", "ret"])
        )
      , ( "Rejecting HUntil Up"
        , False
        , formulaAt 3 $ HUntil Up (Not . Atomic . Prop $ "texc") (Atomic . Prop $ "tend")
        , stlPrecRelV1
        , map (S.fromList . map Prop) (stlAnnotateV1 ["han", "call", "t", "texc", "t", "tend", "ret"])
        )
      , ( "Accepting HUntil Down"
        , True
        , HUntil Down (Atomic . Prop $ "c") (Atomic . Prop $ "cend")
        , stlPrecRelV1
        , map (S.fromList . map Prop) (stlAnnotateV1 ["c", "c", "cend", "call", "thr"])
        )
      , ( "Rejecting Not HUntil Down"
        , False
        , Not ( HUntil Down (Atomic . Prop $ "c") (Atomic . Prop $ "cend"))
        , stlPrecRelV1
        , map (S.fromList . map Prop) (stlAnnotateV1 ["c", "c", "cend", "call", "thr"])
        )
      , ( "Rejecting HUntil Down"
        , False
        , HUntil Down (Not . Atomic . Prop $ "cexc") (Atomic . Prop $ "cend")
        , stlPrecRelV1
        , map (S.fromList . map Prop) (stlAnnotateV1 ["c", "cexc", "cend", "call", "thr"])
        )
      , ( "Accepting HSince Down"
        , True
        , formulaAt 3 $ HSince Down (Atomic . Prop $ "c") (Atomic . Prop $ "cbeg")
        , stlPrecRelV1
        , map (S.fromList . map Prop) (stlAnnotateV1 ["cbeg", "c", "c", "call", "thr"])
        )
      , ( "Rejecting Not HSince Down"
        , False
        , formulaAt 3 $ Not ( HSince Down (Atomic . Prop $ "c") (Atomic . Prop $ "cbeg"))
        , stlPrecRelV1
        , map (S.fromList . map Prop) (stlAnnotateV1 ["cbeg", "c", "c", "call", "thr"])
        )
      , ( "Rejecting HSince Down"
        , False
        , formulaAt 3 $ HSince Down (Not . Atomic . Prop $ "cexc") (Atomic . Prop $ "cbeg")
        , stlPrecRelV1
        , map (S.fromList . map Prop) (stlAnnotateV1 ["cbeg", "cexc", "c", "call", "thr"])
        )
      , ( "Accepting Eventually"
        , True
        , Eventually (Atomic . Prop $ "thr")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "han", "thr", "ret"]
        )
      , ( "Rejecting Not Eventually"
        , False
        , Not $ Eventually (Atomic . Prop $ "thr")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "han", "thr", "ret"]
        )
      , ( "Rejecting Eventually"
        , False
        , Eventually (Atomic . Prop $ "thr")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "han", "ret"]
        )
      , ( "Testing boundaries with XNext"
        , True
        , XNext Up T
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "call"]
        )
      , ( "Testing boundaries with HUntil Down"
        , True
        , HUntil Down T (Atomic . Prop $ "call")
        , stlPrecRelV1
        , map (S.singleton . Prop) ["call", "call"]
        )












      potlv2Tests2 = testGroup "PotlV2, Stack Trace Lang V2, second test group" $ map makeTestCase
      [ ( "Accepting Xor"
        , True
        , (Atomic . Prop $ "call") `Xor` (PNext Down . Atomic . Prop $ "exc")
        , stlPrecRelV2
        , map (S.singleton . Prop) ["call", "han", "exc", "ret"]
        )
      , ( "Rejecting Xor"
        , False
        , (Atomic . Prop $ "call") `Xor` (PNext Down . Atomic . Prop $ "han")
        , stlPrecRelV2
        , map (S.singleton . Prop) ["call", "han", "exc", "ret"]
        )
      , ( "Accepting Implies" -- Ex falso quodlibet ;)
        , True
        , (Atomic . Prop $ "ret") `Implies` (HNext Up . Atomic . Prop $ "han")
        , stlPrecRelV2
        , map (S.singleton . Prop) ["call", "han", "exc", "ret"]
        )
      , ( "Rejecting Implies"
        , False
        , (Atomic . Prop $ "call") `Implies` (PNext Down . Atomic . Prop $ "ret")
        , stlPrecRelV2
        , map (S.singleton . Prop) ["call", "han", "exc", "ret"]
        )
      , ( "Accepting Iff"
        , True
        , (Atomic . Prop $ "call") `Iff` (XNext Up . Atomic . Prop $ "ret")
        , stlPrecRelV2
        , map (S.singleton . Prop) ["call", "han", "exc", "ret"]
        )
      , ( "Rejecting Iff"
        , False
        , (Atomic . Prop $ "call") `Iff` (XNext Up . Atomic . Prop $ "ret")
        , stlPrecRelV2
        , map (S.singleton . Prop) ["call", "han", "exc"]
        )
      , ( "Accepting Eventually"
        , True
        , Eventually . Atomic . Prop $ "ret"
        , stlPrecRelV2
        , map (S.singleton . Prop) ["call", "han", "exc", "ret"]
        )
      , ( "Rejecting Eventually"
        , False
        , Eventually . Atomic . Prop $ "ret"
        , stlPrecRelV2
        , map (S.singleton . Prop) ["call", "han", "exc"]
        )
      , ( "Accepting Always"
        , True
        , Always . Atomic . Prop $ "call"
        , stlPrecRelV2
        , map (S.singleton . Prop) ["call", "call", "call"]
        )
      , ( "Rejecting Always"
        , False
        , Always . Atomic . Prop $ "call"
        , stlPrecRelV2
        , map (S.singleton . Prop) ["call", "han", "call"]
        )
      , ( "Accepting HUntil Down"
        , True
        , PNext Down (HUntil Down T (Atomic . Prop $ "call"))
        , stlPrecRelV2
        , map (S.singleton . Prop) ["han", "call", "call", "call", "exc", "ret"]
        )
      ]
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





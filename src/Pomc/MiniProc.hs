{- |
   Module      : Pomc.MiniProc
   Copyright   : 2020-2025 Michele Chiari
   License     : MIT
   Maintainer  : Michele Chiari
-}

module Pomc.MiniProc ( DeltaTarget(..)
                     , InputLabel(..)
                     , LowerState(..)
                     , Guard(..)
                     , Action(..)
                     , sksToExtendedOpa
                     , programToOpa
                     , miniProcAlphabet
                     , stringToExprPropAlphabet
                     -- Re-exports from MiniIR
                     , Program
                     , FunctionSkeleton(..)
                     , Statement(..)
                     , Variable(..)
                     , IntValue
                     , Expr(..)
                     , LValue(..)
                     , FormalParam(..)
                     , ActualParam(..)
                     , FunctionName
                     , Type(..)
                     , VarState
                     , ExprProp(..)
                     , isSigned
                     , isScalar
                     , isArray
                     , typeWidth
                     , arraySize
                     , scalarType
                     , commonType
                     , varWidth
                     , IdType
                     , VarIdInfo(..)
                     , addVariables
                     ) where

import Pomc.MiniIR
import Pomc.MiniProcUtils
import Pomc.Prop (Prop(..), unprop)
import Pomc.PropConv (APType, PropConv(..), makePropConv, encodeAlphabet)
import Pomc.Prec (Alphabet, Prec(..))
import qualified Pomc.Encoding as E
import Pomc.State (Input, State(..))

import Data.Text (Text)
import qualified Data.Text as T
import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S
import Data.Maybe (isNothing, fromJust)
import Data.Vector (Vector)
import qualified Data.Vector as V

-- import qualified Debug.Trace as DBG

-- Generation of the Extended OPA

-- Data structures
data Guard = NoGuard | Guard Expr deriving Show
data DeltaTarget = EntryStates Text | States [(Guard, Word)] deriving Show
data Action = Noop
  | Assign LValue Expr | Nondet LValue
  | CallOp FunctionName [FormalParam] [ActualParam]
  | Return FunctionName [FormalParam] [ActualParam]
  deriving (Eq, Ord, Show)
data InputLabel = InputLabel { ilStruct :: Text
                             , ilFunction :: FunctionName
                             , ilModules :: [FunctionName]
                             , ilAction :: Action
                             } deriving (Eq, Ord, Show)

data FunctionInfo = FunctionInfo { fiEntry :: [(Guard, Word)]
                                 , fiRetPad :: Word
                                 , fiThrow :: Word
                                 , fiExcPad :: Word
                                 , fiSkeleton :: FunctionSkeleton
                                 } deriving Show
data LowerState = LowerState { lsDPush :: Map Word (InputLabel, DeltaTarget)
                             , lsDShift :: Map Word (InputLabel, DeltaTarget)
                             , lsDPop :: Map (Word, Word) (Action, DeltaTarget)
                             , lsFinfo :: Map Text FunctionInfo
                             , lsSid :: Word
                             } deriving Show

makeInputLabel :: String -> FunctionInfo -> Action -> InputLabel
makeInputLabel sl finfo act = InputLabel (T.pack sl) (skName fsk) (skModules fsk) act
  where fsk = fiSkeleton finfo

sksToExtendedOpa :: Bool -> [FunctionSkeleton] -> (LowerState, [Word], [Word])
sksToExtendedOpa False sks = (buildExtendedOpa sks, [0], [1]) -- Finite case
sksToExtendedOpa True sks = -- Omega case
  let lowerState = buildExtendedOpa sks
      -- Add stuttering transitions
      dPush = M.insert 1 (InputLabel (T.pack "stm") T.empty [] Noop, States [(NoGuard, 1)])
              (lsDPush lowerState)
      dPop = M.insert (1, 1) (Return T.empty [] [], States [(NoGuard, 1)]) (lsDPop lowerState)
  in ( lowerState { lsDPush = dPush, lsDPop = dPop }
     , [0]
     , [0..(lsSid lowerState)] -- all states are final in the Omega case
     )

buildExtendedOpa :: [FunctionSkeleton] -> LowerState
buildExtendedOpa sks =
  let lowerState = lowerFunction sksMap (LowerState M.empty M.empty M.empty M.empty 3) (head sks)
      sksMap = M.fromList $ map (\sk -> (skName sk, sk)) sks
      firstFname = skName $ head sks
      firstFinfo = fromJust $ M.lookup firstFname (lsFinfo lowerState)
      dPush' = M.insert 0
        (InputLabel (T.pack "call") firstFname (skModules $ head sks) (CallOp firstFname [] []),
         EntryStates firstFname) (lsDPush lowerState)
      dPop' = M.insert (fiRetPad firstFinfo, 0) (Return firstFname [] [], States [(NoGuard, 1)])
        (lsDPop lowerState)
      dPop'' = M.insert (fiThrow firstFinfo, 0) (Noop, States [(NoGuard, 2)]) dPop'
      dPush'' = M.insert 2 (InputLabel (T.pack "exc") T.empty [] Noop, States [(NoGuard, 1)]) dPush'
      dPop''' = M.insert (1, 2) (Noop, States [(NoGuard, 1)]) dPop''

      resolveTarget (l, EntryStates fname) =
        (l, States . fiEntry . fromJust $ M.lookup fname (lsFinfo lowerState))
      resolveTarget x = x
      resolveAll deltaMap = M.map resolveTarget deltaMap
  in lowerState { lsDPush = resolveAll dPush''
                , lsDShift = resolveAll $ lsDShift lowerState
                , lsDPop = resolveAll dPop'''
                }

-- Thunk that links a list of states as the successors of the previous statement(s)
type PredLinker = LowerState -> [(Guard, Word)] -> LowerState

dInsert :: (Ord k) => k -> l -> [(Guard, Word)] -> Map k (l, DeltaTarget) -> Map k (l, DeltaTarget)
dInsert _ _ [] delta = delta
dInsert key label states delta =
  case M.lookup key delta of
    Nothing                      -> M.insert key (label, States states) delta
    Just (oldLabel, States olds) -> M.insert key (oldLabel, States $ olds ++ states) delta
    _                            -> error "DeltaTarget mismatch."

lowerFunction :: Map Text FunctionSkeleton
              -> LowerState
              -> FunctionSkeleton
              -> LowerState
lowerFunction sks lowerState0 fsk =
  let sidRet = lsSid lowerState0
      thisFinfo = FunctionInfo [] (sidRet + 1) (sidRet + 2) (sidRet + 3) fsk
      lowerState1 = lowerState0
        { lsFinfo = M.insert (skName fsk) thisFinfo (lsFinfo lowerState0)
        , lsSid = sidRet + 4
        }
      addEntry ls es =
        let tfinfo = fromJust $ M.lookup (skName fsk) (lsFinfo ls)
            finfo1 = M.insert (skName fsk) (tfinfo { fiEntry = (fiEntry tfinfo) ++ es }) (lsFinfo ls)
        in ls { lsFinfo = finfo1 }

      (lowerState2, linkPred) = lowerBlock sks lowerState1 thisFinfo addEntry (skStmts fsk)

      dShift' = M.insert sidRet
        (makeInputLabel "ret" thisFinfo Noop, States [(NoGuard, fiRetPad thisFinfo)])
        (lsDShift lowerState2)
      dShift'' = M.insert (fiThrow thisFinfo)
        (makeInputLabel "exc" thisFinfo Noop, States [(NoGuard, fiExcPad thisFinfo)]) dShift'
  in linkPred (lowerState2 { lsDShift = dShift'' }) [(NoGuard, sidRet)]

lowerStatement :: Map Text FunctionSkeleton
               -> LowerState
               -> FunctionInfo
               -> PredLinker
               -> Statement
               -> (LowerState, PredLinker)
lowerStatement _ lowerState0 thisFinfo linkPred (Assignment lhs rhs) =
  let assSid = lsSid lowerState0
      lowerState1 = linkPred (lowerState0 { lsSid = assSid + 1 }) [(NoGuard, assSid)]
      dPush' = M.insert assSid
        (makeInputLabel "stm" thisFinfo (Assign lhs rhs), States [(NoGuard, assSid)])
        (lsDPush lowerState1)

      linkAss ls succStates =
        let dPop' = dInsert (assSid, assSid) Noop succStates (lsDPop ls)
        in ls { lsDPop = dPop' }

  in (lowerState1 { lsDPush = dPush' }, linkAss)

lowerStatement _ lowerState0 thisFinfo linkPred (Nondeterministic lval) =
  let assSid = lsSid lowerState0
      lowerState1 = linkPred (lowerState0 { lsSid = assSid + 1 }) [(NoGuard, assSid)]
      dPush' = M.insert assSid
        (makeInputLabel "stm" thisFinfo (Nondet lval), States [(NoGuard, assSid)])
        (lsDPush lowerState1)

      linkAss ls succStates =
        let dPop' = dInsert (assSid, assSid) Noop succStates (lsDPop ls)
        in ls { lsDPop = dPop' }

  in (lowerState1 { lsDPush = dPush' }, linkAss)

lowerStatement sks lowerState0 thisFinfo linkPred (Call fname args) =
  let calleeSk = fromJust $ M.lookup fname sks
      callSid = lsSid lowerState0
      calleeFinfo0 = M.lookup fname $ lsFinfo lowerState0
      lowerState1 = lowerState0 { lsSid = callSid + 1 }
      lowerState2 = if isNothing calleeFinfo0
                    then lowerFunction sks lowerState1 calleeSk
                    else lowerState1
      calleeFinfo1 = fromJust $ M.lookup fname (lsFinfo lowerState2)
      dPush'' = M.insert callSid
        (InputLabel (T.pack "call") fname (skModules calleeSk) (CallOp fname (skParams calleeSk) args),
         EntryStates fname)
        (lsDPush lowerState2)
      dPop'' = M.insert (fiThrow calleeFinfo1, callSid)
               (Noop, States [(NoGuard, fiThrow thisFinfo)]) (lsDPop lowerState2)

      linkCall lowerState successorStates =
          let dPop' = dInsert (fiRetPad calleeFinfo1, callSid) (Return fname (skParams calleeSk) args)
                successorStates (lsDPop lowerState)
          in lowerState { lsDPop = dPop' }

      -- TODO: do we really need to increment lsSid here?
      lowerState3 = lowerState2 { lsDPush = dPush'', lsDPop = dPop'', lsSid = lsSid lowerState2 + 1 }
  in (linkPred lowerState3 [(NoGuard, callSid)], linkCall)

lowerStatement _ _ _ _ (Query _ _) =
  error "Query statements not allowed in MiniProc."

lowerStatement sks ls0 thisFinfo linkPred0 (TryCatch try catch) =
  let hanSid = lsSid ls0
      dummySid0 = hanSid + 1
      dummySid1 = dummySid0 + 1
      ls1 = linkPred0 (ls0 { lsSid = dummySid1 + 1 }) [(NoGuard, hanSid)]

      linkHandler lowerState successorStates =
        let dPushH = dInsert hanSid (makeInputLabel "han" thisFinfo Noop)
              successorStates (lsDPush lowerState)
        in lowerState { lsDPush = dPushH }

      (ls2, linkPredTry) = lowerBlock sks ls1 thisFinfo linkHandler try
      -- add dummy exc to exit try block
      ls3 = linkPredTry ls2 [(NoGuard, dummySid0)]
      dShift' = M.insert dummySid0
        (makeInputLabel "exc" thisFinfo Noop, States [(NoGuard, dummySid1)]) (lsDShift ls3)
      ls4 = ls3 { lsDShift = dShift' }

      linkTry lowerState successorStates =
        let dPopD = dInsert (dummySid1, hanSid) Noop successorStates (lsDPop lowerState)
        in lowerState { lsDPop = dPopD }

      linkCatch lowerState successorStates =
        let dPopC = dInsert (fiExcPad thisFinfo, hanSid) Noop successorStates (lsDPop lowerState)
        in lowerState { lsDPop = dPopC }

      (ls5, linkPredCatch) = lowerBlock sks ls4 thisFinfo linkCatch catch

      linkTryCatch ls succStates = linkPredCatch (linkTry ls succStates) succStates
  in (ls5, linkTryCatch)

lowerStatement sks ls0 thisFinfo linkPred0 (IfThenElse guard thenBlock elseBlock) =
  let linkPred0Then lowerState succStates =
        case guard of
          Just bexp -> linkPred0 lowerState (map (\(lbl, s) -> (combGuards bexp lbl, s)) succStates)
          Nothing -> linkPred0 lowerState succStates
      linkPred0Else lowerState succStates =
        case guard of
          Just bexp -> linkPred0 lowerState (map (\(lbl, s) ->
                                                    (combGuards (Not bexp) lbl, s)) succStates)
          Nothing -> linkPred0 lowerState succStates

      (ls1, linkPred1) = lowerBlock sks ls0 thisFinfo linkPred0Then thenBlock
      (ls2, linkPred2) = lowerBlock sks ls1 thisFinfo linkPred0Else elseBlock
      linkPredITE lowerState succStates = linkPred2 (linkPred1 lowerState succStates) succStates
  in (ls2, linkPredITE)

lowerStatement sks ls0 thisFinfo linkPred0 (While guard body) =
  let linkPred1 lowerState0 succStates =
        let enterEdges =
              case guard of
                Just bexp -> map (\(lbl, s) -> (combGuards bexp lbl, s)) succStates
                Nothing -> succStates
        in linkPred0 (linkBody lowerState0 enterEdges) enterEdges

      (ls1, linkBody) = lowerBlock sks ls0 thisFinfo linkPred1 body
      linkPredWhile lowerState succStates =
        let exitEdges = case guard of
                          Just bexp -> map (\(lbl, s) -> (combGuards (Not bexp) lbl, s)) succStates
                          Nothing -> succStates
        in linkBody (linkPred0 lowerState exitEdges) exitEdges
  in (ls1, linkPredWhile)

lowerStatement _ lowerState thisFinfo linkPred (Throw Nothing) =
  (linkPred lowerState [(NoGuard, fiThrow thisFinfo)], (\ls _ -> ls))
lowerStatement _ _ _ _ (Throw _) =
  error "Observe statements not allowed in MiniProc."

lowerStatement _ _ _ _ (Categorical _ _ _) =
  error "Categorical assignments not allowed in MiniProc."

combGuards :: Expr -> Guard -> Guard
combGuards bexp1 NoGuard = Guard bexp1
combGuards bexp1 (Guard bexp2) = Guard (bexp1 `And` bexp2)

lowerBlock :: Map Text FunctionSkeleton
           -> LowerState
           -> FunctionInfo
           -> PredLinker
           -> [Statement]
           -> (LowerState, PredLinker)
lowerBlock _ lowerState _ linkPred [] = (lowerState, linkPred)
lowerBlock sks lowerState thisFinfo linkPred block =
  foldBlock lowerState linkPred block
  where foldBlock lowerState1 linkPred1 [] = (lowerState1, linkPred1)

        foldBlock lowerState1 linkPred1 ((Throw Nothing) : _) =
          let (lowerState2, linkPred2) =
                lowerStatement sks lowerState1 thisFinfo linkPred1 $ Throw Nothing
          in (lowerState2, linkPred2)

        foldBlock lowerState1 linkPred1 (stmt : stmts) =
          let (lowerState2, linkPred2) =
                lowerStatement sks lowerState1 thisFinfo linkPred1 stmt
          in foldBlock lowerState2 linkPred2 stmts

-- Conversion of the Extended OPA to a plain OPA
programToOpa :: Bool -> Program -> Set (Prop ExprProp)
             -> ( PropConv ExprProp
                , Alphabet APType
                , (E.BitEncoding -> Input -> Bool)
                , (E.BitEncoding -> VarState -> State -> Bool)
                , [VarState]
                , VarState -> Bool
                , (E.BitEncoding -> VarState -> Input -> [VarState])
                , (E.BitEncoding -> VarState -> Input -> [VarState])
                , (VarState -> VarState -> [VarState])
                )
programToOpa isOmega prog additionalProps =
  let (lowerState, ini, fin) = sksToExtendedOpa isOmega (pSks prog)
      eInitials = [(sid, initVal) | sid <- ini]
        where (gScalars, gArrays) =
                initialValuation (\_ i -> i) (pGlobalScalars prog) (pGlobalArrays prog)
              initVal = VarValuation { vGlobalScalars = gScalars
                                     , vGlobalArrays = gArrays
                                     , vLocalScalars = V.empty
                                     , vLocalArrays = V.empty
                                     }
      eIsFinal (sid, _) = sid `S.member` finSet
        where finSet = S.fromList fin

      allProps = foldr S.insert additionalProps $ fst miniProcAlphabet
      pconv = makePropConv $ S.toList allProps
      gvii = VarIdInfo { scalarOffset = sids, arrayOffset = aids, varIds = sids + aids }
        where sids = S.size . pGlobalScalars $ prog
              aids = S.size . pGlobalArrays $ prog
      localsInfo = M.insert T.empty (globExprMap, V.empty, V.empty)
        $ M.fromList
        $ map (\sk -> let (liScalars, liArrays) =
                            initialValuation (getLocalIdx gvii) (skScalars sk) (skArrays sk)
                          exprMap = makeExprPropMap (Just . skName $ sk)
                                    `M.union` globExprMap
                      in (skName sk, (exprMap, liScalars, liArrays)))
        $ pSks prog
        where makeExprPropMap scope = M.fromList
                $ map (\p -> (encodeProp pconv p, getExpr . unprop $ p))
                $ filter filterExpr
                $ S.toList additionalProps
                where filterExpr (Prop (ExprProp s _)) | s == scope = True
                      filterExpr _ = False
              globExprMap = makeExprPropMap Nothing
      remapDelta delta =
        M.map (\(ilabel, States s) -> (ilabelToPropSet ilabel, ilabel, s)) delta
        where ilabelToPropSet il = S.fromList
                $ map (encodeProp pconv)
                $ filter (`S.member` allProps)
                $ map (Prop . TextProp) $ ilStruct il : ilFunction il : ilModules il
      remappedDPush = remapDelta $ lsDPush lowerState
      remappedDShift = remapDelta $ lsDShift lowerState
      decodeDeltaInput remappedDelta bitenc q b =
        applyDeltaInput gvii localsInfo remappedDelta q $ E.decodeInput bitenc b

      inputFilter bitenc b =
        let pLabels = map (\(l, _, _) -> l) $ M.elems remappedDPush
            sLabels = map (\(l, _, _) -> l) $ M.elems remappedDShift
            labels = S.insert (E.encodeInput bitenc S.empty)
              $ S.fromList $ map (E.encodeInput bitenc) $ pLabels ++ sLabels
            lmask = S.foldl E.union (E.encodeInput bitenc S.empty) labels
        in (b `E.intersect` lmask) `S.member` labels

      stateFilter bitenc q@(sid, _) atom =
        sid `S.member` popStates
        || (not $ null $ decodeDeltaInput remappedDPush bitenc q b)
        || (not $ null $ decodeDeltaInput remappedDShift bitenc q b)
        where b = E.extractInput bitenc $ current atom
              popStates = S.map fst $ M.keysSet $ lsDPop lowerState

  in ( pconv
     , encodeAlphabet pconv miniProcAlphabet
     , inputFilter
     , stateFilter
     , eInitials
     , if isOmega then const True else eIsFinal
     , decodeDeltaInput remappedDPush
     , decodeDeltaInput remappedDShift
     , applyDeltaPop gvii $ lsDPop lowerState
     )

applyDeltaInput :: VarIdInfo
                -> Map FunctionName (Map (Prop APType) Expr, Vector IntValue, Vector ArrayValue)
                -> Map Word (Set (Prop APType), InputLabel, [(Guard, Word)])
                -> VarState
                -> Set (Prop APType)
                -> [VarState]
applyDeltaInput gvii localsInfo delta (sid, svval) lbl =
  case M.lookup sid delta of
    Nothing -> []
    Just (lsProps, il, dsts) ->
      let (exprPropMap, initScalars, initArrays) = localsInfo M.! ilFunction il
          callVval = prepareForCall (ilAction il) initScalars initArrays
          trueExprProps = M.keysSet $ M.filter (toBool . evalExpr gvii callVval) exprPropMap
      in if (trueExprProps, lsProps) == S.partition (`M.member` exprPropMap) lbl
         then computeDsts gvii callVval (ilAction il) dsts
         else []
  where prepareForCall (CallOp _ fargs aargs) initScalars initArrays =
          let newVval = svval { vLocalScalars = initScalars
                              , vLocalArrays = initArrays
                              }
              evalArg vval (Value fvar, ActualVal expr)
                | isScalar . varType $ fvar =
                    scalarAssign gvii vval fvar $ evalExpr gvii svval expr
                | otherwise = let (Term avar) = expr
                              in wholeArrayAssign gvii vval fvar svval avar
              evalArg vval (ValueResult fvar, ActualValRes avar)
                | isScalar . varType $ fvar =
                    scalarAssign gvii vval fvar $ evalExpr gvii svval (Term avar)
                | otherwise = wholeArrayAssign gvii vval fvar svval avar
              evalArg _ _ = error "Argument passing mode mismatch."
          in foldl evalArg newVval $ zip fargs aargs
        prepareForCall _ _ _ = svval

applyDeltaPop :: VarIdInfo
              -> Map (Word, Word) (Action, DeltaTarget)
              -> VarState
              -> VarState
              -> [VarState]
applyDeltaPop gvii delta (sid, svval) (stackSid, stackVval) =
  case M.lookup (sid, stackSid) delta of
    Nothing                      -> []
    Just (Return _ fargs aargs, States dsts) ->
      let newVval = svval { vLocalScalars = vLocalScalars stackVval
                          , vLocalArrays = vLocalArrays stackVval
                          }
          retArg vval (ValueResult fvar, ActualValRes avar)
            | isScalar . varType $ fvar =
                scalarAssign gvii vval avar $ evalExpr gvii svval (Term fvar)
            | otherwise = wholeArrayAssign gvii vval avar svval fvar
          retArg vval _ = vval
          retVval = foldl retArg newVval $ zip fargs aargs
      in computeDsts gvii retVval Noop dsts
    Just (_, States dsts)        -> computeDsts gvii svval Noop dsts
    Just (_, EntryStates _)      -> error "Expected States, got EntryStates."

computeDsts :: VarIdInfo -> VarValuation -> Action -> [(Guard, Word)] -> [VarState]
computeDsts gvii vval act dsts = concatMap composeDst dsts
  where composeDst (NoGuard, dst) = map (\newVval -> (dst, newVval)) newVvals
        composeDst (Guard g, dst)
          | toBool $ evalExpr gvii vval g = map (\newVval -> (dst, newVval)) newVvals
          | otherwise = []
        newVvals = case act of
          Noop -> [vval]
          CallOp {} -> [vval]
          Return {} -> [vval]
          Assign (LScalar lhs) rhs -> [scalarAssign gvii vval lhs $ evalExpr gvii vval rhs]
          Assign (LArray var idxExpr) rhs ->
            [arrayAssign gvii vval var idxExpr $ evalExpr gvii vval rhs]
          Nondet (LScalar var) ->
            map (\val -> scalarAssign gvii vval var val) $ enumerateIntType (varType var)
          Nondet (LArray var idxExpr) ->
            map (\val -> arrayAssign gvii vval var idxExpr val) $ enumerateIntType (varType var)


-- OPM
miniProcAlphabet :: Alphabet ExprProp
miniProcAlphabet = stringToExprPropAlphabet miniProcStringAlphabet

miniProcStringAlphabet :: Alphabet String
miniProcStringAlphabet = (miniProcSls, miniProcPrecRel)
  where miniProcSls = map Prop ["call", "ret", "han", "exc", "stm"]
        miniProcPrecRel =
          map (\(sl1, sl2, pr) -> (Prop sl1, Prop sl2, pr)) precs
          ++ map (\p -> (p, End, Take)) miniProcSls
          where precs = [ ("call", "call", Yield)
                        , ("call", "ret",  Equal)
                        , ("call", "han",  Yield)
                        , ("call", "exc",  Take)
                        , ("call", "stm",  Yield)
                        , ("ret",  "call", Take)
                        , ("ret",  "ret",  Take)
                        , ("ret",  "han",  Take)
                        , ("ret",  "exc",  Take)
                        , ("ret",  "stm",  Take)
                        , ("han",  "call", Yield)
                        , ("han",  "ret",  Take)
                        , ("han",  "han",  Yield)
                        , ("han",  "exc",  Equal)
                        , ("han",  "stm",  Yield)
                        , ("exc",  "call", Take)
                        , ("exc",  "ret",  Take)
                        , ("exc",  "han",  Take)
                        , ("exc",  "exc",  Take)
                        , ("exc",  "stm",  Take)
                        , ("stm",  "call", Take)
                        , ("stm",  "ret",  Take)
                        , ("stm",  "han",  Take)
                        , ("stm",  "exc",  Take)
                        , ("stm",  "stm",  Take)
                        ]

stringToExprPropAlphabet :: Alphabet String -> Alphabet ExprProp
stringToExprPropAlphabet (stringSls, stringPrecRel) = (epSls, epPrecRel) where
  epSls = map toExprProp stringSls
  epPrecRel =
    map (\(sl1, sl2, pr) -> (toExprProp sl1, toExprProp sl2, pr)) stringPrecRel
  toExprProp = fmap (TextProp . T.pack)

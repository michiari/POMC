{- |
   Module      : Pomc.Prob.MiniProb
   Copyright   : 2020-2023 Michele Chiari
   License     : MIT
   Maintainer  : Michele Chiari
-}

module Pomc.Prob.MiniProb ( Popa(..)
                          , Program
                          , ExprProp
                          , programToPopa
                          -- TODO: remove the following eventually
                          , sksToExtendedOpa
                          , LowerState(..)
                          ) where

import Pomc.MiniIR
import Pomc.MiniProcUtils
import Pomc.Prop (Prop(..), unprop)
import Pomc.PropConv (APType, PropConv(..), makePropConv, encodeAlphabet)
import Pomc.Prec (Alphabet)
import qualified Pomc.Encoding as E
import Pomc.Prob.ProbUtils (Prob, Label, RichDistr)

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

data Popa s a = Popa
  { popaAlphabet   :: Alphabet a -- OP alphabet
  , popaInitial    :: E.BitEncoding -> (s, Label) -- initial state of the POPA
  , popaDeltaPush  :: E.BitEncoding -> s -> RichDistr s Label -- push transition prob. distribution
  , popaDeltaShift :: E.BitEncoding -> s -> RichDistr s Label -- shift transition prob. distribution
  , popaDeltaPop   :: E.BitEncoding -> s -> s -> RichDistr s Label -- pop transition prob. distribution
  }

-- Generation of the Extended OPA

-- Data structures
data Action = Assign LValue Expr
  | Cat LValue [(Expr, Prob)]
  | CallOp FunctionName [FormalParam] [ActualParam]
  | Return
  | Handle
  | ExcThrow
  | Flush
  deriving (Eq, Ord, Show)
data PState = PState { psId :: Word
                     , psLabels :: (FunctionName, [FunctionName])
                     , psAction :: Action
                     } deriving (Eq, Ord, Show)
data DeltaTarget = EntryStates FunctionName
  | Det PState
  | Guard [(Expr, PState)] deriving Show
data RetInfo = NoRet | RetInfo [FormalParam] [ActualParam] deriving Show
data FunctionInfo = FunctionInfo { fiEntry :: Maybe DeltaTarget
                                 , fiRetPad :: PState
                                 , fiThrow :: PState
                                 , fiExcPad :: PState
                                 , fiSkeleton :: FunctionSkeleton
                                 } deriving Show
data LowerState = LowerState { lsDPush :: Map Word (PState, DeltaTarget) -- TODO maybe we just need the Action here
                             , lsDShift :: Map Word (PState, DeltaTarget)
                             , lsDPop :: Map (Word, Word) (RetInfo, DeltaTarget)
                             , lsFinfo :: Map Text FunctionInfo
                             , lsSid :: Word
                             } deriving Show

sksToExtendedOpa :: Bool -> [FunctionSkeleton] -> (LowerState, PState)
sksToExtendedOpa False sks = buildExtendedOpa sks -- Finite case
sksToExtendedOpa True _sks = error "Omega case not implemented for probabilistic programs."

buildExtendedOpa :: [FunctionSkeleton] -> (LowerState, PState)
buildExtendedOpa sks =
  let lowerState = lowerFunction sksMap (LowerState M.empty M.empty M.empty M.empty 3) (head sks)
      sksMap = M.fromList $ map (\sk -> (skName sk, sk)) sks
      firstFname = skName $ head sks
      firstFinfo = lsFinfo lowerState M.! firstFname
      firstCall = PState 0 (firstFname, skModules $ head sks) (CallOp firstFname [] [])
      dPush' = M.insert 0 (firstCall, EntryStates firstFname) (lsDPush lowerState)
      popLast = PState 1 (T.empty, []) Flush
      dPop' = M.insert (psId $ fiRetPad firstFinfo, 0) (RetInfo [] [], Det popLast)
              (lsDPop lowerState)
      uncaughtExc = PState 2 (T.empty, []) ExcThrow
      dPop'' = M.insert (psId $ fiThrow firstFinfo, 0) (NoRet, Det uncaughtExc) dPop'
      dPush'' = M.insert 2 (uncaughtExc, Det popLast) dPush'
      dPop''' = M.insert (1, 2) (NoRet, Det popLast) dPop''

      resolveTarget (l, EntryStates fname) = (l, fromJust . fiEntry $ lsFinfo lowerState M.! fname)
      resolveTarget x = x
      resolveAll deltaMap = M.map resolveTarget deltaMap
  in ( lowerState { lsDPush = resolveAll dPush''
                  , lsDShift = resolveAll $ lsDShift lowerState
                  , lsDPop = resolveAll dPop'''
                  }
     , firstCall
     )

-- Thunk that links a list of states as the successors of the previous statement(s)
type PredLinker = LowerState -> DeltaTarget -> LowerState

mergeDts :: DeltaTarget -> Maybe DeltaTarget -> Maybe DeltaTarget
mergeDts dt Nothing = Just dt
mergeDts (Guard news) (Just (Guard olds)) = Just . Guard $ olds ++ news
mergeDts _ _ = error "DeltaTarget mismatch."

dInsert :: (Ord k) => k -> l -> DeltaTarget -> Map k (l, DeltaTarget) -> Map k (l, DeltaTarget)
dInsert key label dt delta =
  M.alter (fmap (\ndt -> (label, ndt)) . mergeDts dt . fmap snd) key delta

mkPSLabels :: FunctionSkeleton -> (FunctionName, [FunctionName])
mkPSLabels fsk = (skName fsk, skModules fsk)

lowerFunction :: Map Text FunctionSkeleton
              -> LowerState
              -> FunctionSkeleton
              -> LowerState
lowerFunction sks lowerState0 fsk =
  let retSid = lsSid lowerState0
      retState = PState retSid (mkPSLabels fsk) Return
      thisFinfo = FunctionInfo
        { fiEntry = Nothing
        , fiRetPad = PState (retSid + 1) (mkPSLabels fsk) Return
        , fiThrow = PState (retSid + 2) (mkPSLabels fsk) ExcThrow
        , fiExcPad = PState (retSid + 3) (mkPSLabels fsk) ExcThrow
        , fiSkeleton = fsk
        }
      lowerState1 = lowerState0
        { lsFinfo = M.insert (skName fsk) thisFinfo (lsFinfo lowerState0)
        , lsSid = retSid + 4
        }
      addEntry ls es = ls
        { lsFinfo = M.adjust (\tfinfo -> tfinfo { fiEntry = mergeDts es (fiEntry tfinfo) })
                    (skName fsk) (lsFinfo ls)
        }

      (lowerState2, linkPred) = lowerBlock sks lowerState1 thisFinfo addEntry (skStmts fsk)

      dShift' = M.insert retSid (retState, Det $ fiRetPad thisFinfo) (lsDShift lowerState2)
      dShift'' = M.insert (psId $ fiThrow thisFinfo)
                 (fiThrow thisFinfo, Det $ fiExcPad thisFinfo) dShift'
  in linkPred (lowerState2 { lsDShift = dShift'' }) (Det retState)

lowerStatement :: Map Text FunctionSkeleton
               -> LowerState
               -> FunctionInfo
               -> PredLinker
               -> Statement
               -> (LowerState, PredLinker)
lowerStatement _ lowerState0 thisFinfo linkPred (Assignment lhs rhs) =
  let assSid = lsSid lowerState0
      assState = PState assSid (mkPSLabels $ fiSkeleton thisFinfo) (Assign lhs rhs)
      lowerState1 = linkPred (lowerState0 { lsSid = assSid + 1 }) (Det assState)
      dPush' = M.insert assSid (assState, Det assState) (lsDPush lowerState1)

      linkAss ls succStates = ls { lsDPop = dInsert (assSid, assSid) NoRet succStates (lsDPop ls) }

  in (lowerState1 { lsDPush = dPush' }, linkAss)

lowerStatement _ _ _ _ (Nondeterministic _) =
  error "Nondeterministic assignments not allowed in probabilistic programs."

lowerStatement _ ls0 thisFinfo linkPred (Categorical lhs exprs probs) =
  let exprProbs = zip exprs $ probs ++ [1 - (sum probs)]
      catSid = lsSid ls0
      catState = PState catSid (mkPSLabels $ fiSkeleton thisFinfo) (Cat lhs exprProbs)
      lowerState1 = linkPred (ls0 { lsSid = catSid + 1 }) (Det catState)
      dPush' = M.insert catSid (catState, Det catState) (lsDPush lowerState1)

      linkCat ls succStates = ls { lsDPop = dInsert (catSid, catSid) NoRet succStates (lsDPop ls) }

  in (lowerState1 { lsDPush = dPush' }, linkCat)

lowerStatement sks lowerState0 thisFinfo linkPred (Call fname args) =
  let calleeSk = sks M.! fname
      callSid = lsSid lowerState0
      callState = PState callSid (mkPSLabels calleeSk) (CallOp fname (skParams calleeSk) args)
      calleeFinfo0 = M.lookup fname $ lsFinfo lowerState0
      lowerState1 = lowerState0 { lsSid = callSid + 1 }
      lowerState2 = if isNothing calleeFinfo0
                    then lowerFunction sks lowerState1 calleeSk
                    else lowerState1
      calleeFinfo1 = lsFinfo lowerState2 M.! fname
      dPush'' = M.insert callSid (callState, EntryStates fname) (lsDPush lowerState2)
      dPop'' = M.insert (psId $ fiThrow calleeFinfo1, callSid)
               (NoRet, Det $ fiThrow thisFinfo) (lsDPop lowerState2)

      linkCall lowerState successorStates = lowerState
        { lsDPop = dInsert (psId $ fiRetPad calleeFinfo1, callSid)
                   (RetInfo (skParams calleeSk) args)
                   successorStates (lsDPop lowerState)
        }

      lowerState3 = lowerState2 { lsDPush = dPush'', lsDPop = dPop'', lsSid = lsSid lowerState2 + 1 }
  in (linkPred lowerState3 (Det callState), linkCall)

lowerStatement sks ls0 thisFinfo linkPred0 (TryCatch try catch) =
  let fsk = fiSkeleton thisFinfo
      hanSid = lsSid ls0
      hanState = PState hanSid (mkPSLabels fsk) Handle
      dummySid0 = hanSid + 1
      dummyState0 = PState dummySid0 (mkPSLabels fsk) ExcThrow
      dummySid1 = dummySid0 + 1
      dummyState1 = PState dummySid1 (mkPSLabels fsk) ExcThrow -- TODO should not be an exc (maybe #?)
      ls1 = linkPred0 (ls0 { lsSid = dummySid1 + 1 }) (Det hanState)

      linkHandler lowerState successorStates =
        lowerState { lsDPush = dInsert hanSid hanState successorStates (lsDPush lowerState) }

      (ls2, linkPredTry) = lowerBlock sks ls1 thisFinfo linkHandler try
      -- add dummy exc to exit try block
      ls3 = linkPredTry ls2 (Det dummyState0)
      ls4 = ls3 { lsDShift = M.insert dummySid0 (dummyState0, Det dummyState1) (lsDShift ls3) }

      linkTry lowerState successorStates = lowerState
        { lsDPop = dInsert (dummySid1, hanSid) NoRet successorStates (lsDPop lowerState) }

      linkCatch lowerState succDt = lowerState
        { lsDPop = dInsert (psId $ fiExcPad thisFinfo, hanSid) NoRet succDt (lsDPop lowerState) }

      (ls5, linkPredCatch) = lowerBlock sks ls4 thisFinfo linkCatch catch

      linkTryCatch ls succStates = linkPredCatch (linkTry ls succStates) succStates
  in (ls5, linkTryCatch)

lowerStatement sks ls0 thisFinfo linkPred0 (IfThenElse (Just bexp) thenBlock elseBlock) =
  let linkPred0Then lowerState succStates = linkPred0 lowerState (combGuards bexp succStates)
      linkPred0Else lowerState succStates = linkPred0 lowerState (combGuards (Not bexp) succStates)

      (ls1, linkPred1) = lowerBlock sks ls0 thisFinfo linkPred0Then thenBlock
      (ls2, linkPred2) = lowerBlock sks ls1 thisFinfo linkPred0Else elseBlock
      linkPredITE lowerState succStates = linkPred2 (linkPred1 lowerState succStates) succStates
  in (ls2, linkPredITE)
lowerStatement _ _ _ _ (IfThenElse Nothing _ _) =
  error "Nondeterministic guards not allowed in probabilistic programs."

lowerStatement sks ls0 thisFinfo linkPred0 (While (Just bexp) body) =
  let linkPred1 lowerState0 succStates =
        let enterEdges = combGuards bexp succStates
        in linkPred0 (linkBody lowerState0 enterEdges) enterEdges

      (ls1, linkBody) = lowerBlock sks ls0 thisFinfo linkPred1 body
      linkPredWhile lowerState succStates =
        let exitEdges = combGuards (Not bexp) succStates
        in linkBody (linkPred0 lowerState exitEdges) exitEdges
  in (ls1, linkPredWhile)
lowerStatement _ _ _ _ (While Nothing _) =
  error "Nondeterministic guards not allowed in probabilistic programs."

lowerStatement _ lowerState thisFinfo linkPred Throw =
  (linkPred lowerState (Det $ fiThrow thisFinfo), (\ls _ -> ls))

combGuards :: Expr -> DeltaTarget -> DeltaTarget
combGuards bexp1 (Det ps) = Guard [(bexp1, ps)]
combGuards bexp1 (Guard targets) =
  Guard $ map (\(bexp2, ps) -> ((bexp1 `And` bexp2), ps)) targets
combGuards _ _ = error "DeltaTarget mismatch."

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

        foldBlock lowerState1 linkPred1 (Throw : _) =
          let (lowerState2, linkPred2) =
                lowerStatement sks lowerState1 thisFinfo linkPred1 Throw
          in (lowerState2, linkPred2)

        foldBlock lowerState1 linkPred1 (stmt : stmts) =
          let (lowerState2, linkPred2) =
                lowerStatement sks lowerState1 thisFinfo linkPred1 stmt
          in foldBlock lowerState2 linkPred2 stmts

-- Conversion of the Extended pOPA to a plain pOPA
programToPopa :: Bool -> Program -> Set (Prop ExprProp)
              -> ( PropConv ExprProp
                 , Popa VarState APType
                 )
programToPopa isOmega prog additionalProps =
  let (lowerState, ini) = sksToExtendedOpa isOmega (pSks prog)

      allProps = foldr S.insert additionalProps miniProcSls
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
      eInitial = (psId ini, initVal)
        where (gScalars, gArrays) =
                initialValuation (\_ i -> i) (pGlobalScalars prog) (pGlobalArrays prog)
              (_, lScalars, lArrays) = localsInfo M.! fst (psLabels ini)
              initVal = VarValuation { vGlobalScalars = gScalars
                                     , vGlobalArrays = gArrays
                                     , vLocalScalars = lScalars
                                     , vLocalArrays = lArrays
                                     }

  in ( pconv
     , Popa { popaAlphabet = encodeAlphabet pconv miniProcAlphabet
            , popaInitial = (\bitenc -> (eInitial, pStateToLabel bitenc pconv allProps gvii localsInfo ini $ snd eInitial))
            , popaDeltaPush = applyDeltaInput pconv allProps gvii localsInfo
                              $ lsDPush lowerState
            , popaDeltaShift = applyDeltaInput pconv allProps gvii localsInfo
                               $ lsDShift lowerState
            , popaDeltaPop = applyDeltaPop pconv allProps gvii localsInfo
                             $ lsDPop lowerState
            }
     )
     -- TODO check if we still need the inputFilter
     -- TODO check if we still need the stateFilter

applyDeltaInput :: PropConv ExprProp
                -> Set (Prop ExprProp)
                -> VarIdInfo
                -> Map FunctionName (Map (Prop APType) Expr, Vector IntValue, Vector ArrayValue)
                -> Map Word (PState, DeltaTarget)
                -> E.BitEncoding
                -> VarState
                -> RichDistr VarState Label
applyDeltaInput pconv allProps gvii localsInfo delta bitenc (sid, svval) =
  case M.lookup sid delta of
    Nothing -> error "Unexpected dead state"
    Just (ps, dt) -> computeDsts bitenc pconv allProps gvii localsInfo svval (psAction ps) dt

applyDeltaPop :: PropConv ExprProp
              -> Set (Prop ExprProp)
              -> VarIdInfo
              -> Map FunctionName (Map (Prop APType) Expr, Vector IntValue, Vector ArrayValue)
              -> Map (Word, Word) (RetInfo, DeltaTarget)
              -> E.BitEncoding
              -> VarState
              -> VarState
              -> RichDistr VarState Label
applyDeltaPop pconv allProps gvii localsInfo delta bitenc (sid, svval) (stackSid, stackVval) =
  case M.lookup (sid, stackSid) delta of
    Nothing -> error "Unexpected dead state"
    Just (RetInfo fargs aargs, dt) ->
      let newVval = svval { vLocalScalars = vLocalScalars stackVval
                          , vLocalArrays = vLocalArrays stackVval
                          }
          retArg vval (ValueResult fvar, ActualValRes avar)
            | isScalar . varType $ fvar =
                scalarAssign gvii vval avar $ evalExpr gvii svval (Term fvar)
            | otherwise = wholeArrayAssign gvii vval avar svval fvar
          retArg vval _ = vval
          retVval = foldl retArg newVval $ zip fargs aargs
      in computeDsts bitenc pconv allProps gvii localsInfo retVval Return dt
    Just (NoRet, dt) -> computeDsts bitenc pconv allProps gvii localsInfo svval Return dt

computeDsts :: E.BitEncoding
            -> PropConv ExprProp
            -> Set (Prop ExprProp)
            -> VarIdInfo
            -> Map FunctionName (Map (Prop APType) Expr, Vector IntValue, Vector ArrayValue)
            -> VarValuation
            -> Action
            -> DeltaTarget
            -> RichDistr VarState Label
computeDsts bitenc pconv allProps gvii localsInfo vval act dt =
  let newDsts = case dt of
        Det ps -> map (\(newVval, prob) -> ((ps, newVval), prob)) newVvals
        Guard dsts -> concatMap composeDst dsts
        EntryStates _ -> error "Unexpected EntryStates"
  in map (\((ps, vval0), prob) ->
            let vval1 = prepareForCall (psAction ps) (fst $ psLabels ps) vval0
            in ( (psId ps, vval1)
               , pStateToLabel bitenc pconv allProps gvii localsInfo ps vval1
               , prob
               )
         ) -- Calls must be evaluated immediately, other actions will be in the next state
     newDsts
  where composeDst (g, dst)
          | toBool $ evalExpr gvii vval g =
              map (\(newVval, prob) -> ((dst, newVval), prob)) newVvals
          | otherwise = []
        newVvals = case act of
          Assign (LScalar lhs) rhs -> [(scalarAssign gvii vval lhs $ evalExpr gvii vval rhs, 1)]
          Assign (LArray var idxExpr) rhs ->
            [(arrayAssign gvii vval var idxExpr $ evalExpr gvii vval rhs, 1)]
          Cat (LScalar lhs) rhs ->
            map (\(expr, prob) ->
                   (scalarAssign gvii vval lhs $ evalExpr gvii vval expr, prob))
            rhs
          Cat (LArray var idxExpr) rhs ->
            map (\(expr, prob) ->
                   (arrayAssign gvii vval var idxExpr $ evalExpr gvii vval expr, prob))
            rhs
          _ -> [(vval, 1)]

        prepareForCall :: Action -> FunctionName -> VarValuation -> VarValuation
        prepareForCall (CallOp _ fargs aargs) fname svval =
          let (_, initScalars, initArrays) = localsInfo M.! fname
              newVval = svval { vLocalScalars = initScalars
                              , vLocalArrays = initArrays
                              }
              evalArg avval (Value fvar, ActualVal expr)
                | isScalar . varType $ fvar =
                    scalarAssign gvii avval fvar $ evalExpr gvii svval expr
                | otherwise = let (Term avar) = expr
                              in wholeArrayAssign gvii avval fvar svval avar
              evalArg avval (ValueResult fvar, ActualValRes avar)
                | isScalar . varType $ fvar =
                    scalarAssign gvii avval fvar $ evalExpr gvii svval (Term avar)
                | otherwise = wholeArrayAssign gvii avval fvar svval avar
              evalArg _ _ = error "Argument passing mode mismatch."
          in foldl evalArg newVval $ zip fargs aargs
        prepareForCall _ _ svval = svval

pStateToLabel :: E.BitEncoding
              -> PropConv ExprProp
              -> Set (Prop ExprProp)
              -> VarIdInfo
              -> Map FunctionName (Map (Prop APType) Expr, Vector IntValue, Vector ArrayValue)
              -> PState -> VarValuation -> Label
pStateToLabel bitenc pconv allProps gvii localsInfo ps svval =
  let (exprPropMap, _, _) = localsInfo M.! (fst $ psLabels ps)
      trueExprProps = M.keysSet $ M.filter (toBool . evalExpr gvii svval) exprPropMap
      lsProps = S.fromList
                $ map (encodeProp pconv)
                $ filter (`S.member` allProps)
                $ (actionStruct $ psAction ps)
                : (map (Prop . TextProp) $ (fst $ psLabels ps) : (snd $ psLabels ps))
  in E.encodeInput bitenc $ lsProps `S.union` trueExprProps

actionStruct :: Action -> Prop ExprProp
actionStruct Flush = End
actionStruct ac = Prop . TextProp . T.pack $ case ac of
  Assign {} -> "stm"
  Cat {}    -> "stm"
  CallOp {} -> "call"
  Return    -> "ret"
  Handle    -> "han"
  ExcThrow  -> "exc"

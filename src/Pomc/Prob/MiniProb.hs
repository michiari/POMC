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
import Pomc.Prec (Prec(..), StructPrecRel, Alphabet)
import qualified Pomc.Encoding as E
import Pomc.Prob.ProbUtils (Label, RichDistr)

import Data.Ratio ((%))
import qualified Data.BitVector as B
import Data.Text (Text)
import qualified Data.Text as T
import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S
import Data.Maybe (fromJust)
import Data.Vector (Vector)
import qualified Data.Vector as V
import Control.Monad.State.Lazy (State, runState, get, gets, modify)
import Control.Monad (when, foldM)

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
  | Cat LValue [Expr] [(Expr, Expr)] -- lhs [rhs] [(num, den)]
  | Unif LValue Expr Expr
  | CallOp FunctionName [FormalParam] [ActualParam]
  | Return
  | StartQuery
  | ThrowObs
  | Stutter
  deriving (Eq, Ord, Show)
data PState = PState { psId :: Word
                     , psLabels :: (FunctionName, [FunctionName])
                     , psAction :: Action
                     } deriving (Eq, Ord, Show)
data DeltaTarget = EntryStates FunctionName
  | Det PState
  | Guard [(Expr, PState)] deriving Show
data EntryTarget = Known DeltaTarget | Thunk (DeltaTarget -> DeltaTarget)
data RetInfo = NoRet | RetInfo [FormalParam] [ActualParam] | RetObs deriving Show
data FunctionInfo = FunctionInfo { fiEntry :: Maybe DeltaTarget
                                 , fiRetPad :: PState
                                 , fiThrow :: PState
                                 , fiSkeleton :: FunctionSkeleton
                                 } deriving Show
data LowerState = LowerState { lsDPush :: Map Word (Action, DeltaTarget)
                             , lsDShift :: Map Word (Action, DeltaTarget)
                             , lsDPop :: Map (Word, Word) (RetInfo, DeltaTarget)
                             , lsFinfo :: Map Text FunctionInfo
                             , lsSid :: Word
                             } deriving Show

insertPush :: Word -> (Action, DeltaTarget) -> State LowerState ()
insertPush key val =
  modify (\ls -> ls { lsDPush = M.insert key val $ lsDPush ls })

insertShift :: Word -> (Action, DeltaTarget) -> State LowerState ()
insertShift key val =
  modify (\ls -> ls { lsDShift = M.insert key val $ lsDShift ls })

insertPop :: (Word, Word) -> (RetInfo, DeltaTarget) -> State LowerState ()
insertPop key val =
  modify (\ls -> ls { lsDPop = M.insert key val $ lsDPop ls })

getSid :: State LowerState Word
getSid = lsSid <$> get

getSidInc :: State LowerState Word
getSidInc = do
  oldSid <- gets lsSid
  modify (\ls -> ls { lsSid = oldSid + 1 })
  return oldSid

sksToExtendedOpa :: [FunctionSkeleton] -> (PState, LowerState)
sksToExtendedOpa sks = flip runState (LowerState M.empty M.empty M.empty M.empty 3) $ do
  let sksMap = M.fromList $ map (\sk -> (skName sk, sk)) sks
  lowerFunction sksMap (head sks)

  let firstFname = skName $ head sks
  firstFinfo <- (M.! firstFname) . lsFinfo <$> get
  let firstCall = PState 0 (firstFname, skModules $ head sks) (CallOp firstFname [] [])
  insertPush 0 (psAction firstCall, EntryStates firstFname)

  let stutter = PState 1 (T.empty, []) Stutter
  insertPop (psId $ fiRetPad firstFinfo, 0) (RetInfo [] [], Det stutter)

  -- Add stuttering transitions
  insertPush 1 (psAction stutter, Det stutter)
  insertPop (1, 1) (NoRet, Det stutter)

  let uncaughtObs = PState 2 (T.empty, []) ThrowObs
  insertPop (psId $ fiThrow firstFinfo, 0) (NoRet, Det uncaughtObs)
  insertPush 2 (psAction uncaughtObs, Det stutter)
  insertPop (1, 2) (NoRet, Det stutter)

  finfo <- lsFinfo <$> get
  let resolveTarget (l, EntryStates fname) =
        (l, fromJust . fiEntry $ finfo M.! fname)
      resolveTarget x = x
      resolveAll deltaMap = M.map resolveTarget deltaMap
  modify (\ls -> ls { lsDPush  = resolveAll $ lsDPush ls
                    , lsDShift = resolveAll $ lsDShift ls
                    , lsDPop   = resolveAll $ lsDPop ls
                    })
  return firstCall

-- Thunk that links a list of states as the successors of the previous statement(s)
type PredLinker = DeltaTarget -> State LowerState ()

mergeDts :: DeltaTarget -> Maybe DeltaTarget -> DeltaTarget
mergeDts dt Nothing = dt
mergeDts (Guard news) (Just (Guard olds)) = Guard $ olds ++ news
mergeDts _ _ = error "DeltaTarget mismatch."

dInsert :: (Ord k) => k -> l -> DeltaTarget
        -> Map k (l, DeltaTarget) -> Map k (l, DeltaTarget)
dInsert key label dt delta =
  M.alter (Just . (\dts -> (label, dts)) . mergeDts dt . fmap snd) key delta

addPops :: (Word, Word) -> RetInfo -> DeltaTarget -> State LowerState ()
addPops key label dt =
  modify (\ls -> ls { lsDPop = dInsert key label dt $ lsDPop ls })

addPushes :: Word -> Action -> DeltaTarget -> State LowerState ()
addPushes key label dt =
  modify (\ls -> ls { lsDPush = dInsert key label dt $ lsDPush ls })

mkPSLabels :: FunctionSkeleton -> (FunctionName, [FunctionName])
mkPSLabels fsk = (skName fsk, skModules fsk)

lowerFunction :: Map Text FunctionSkeleton
              -> FunctionSkeleton
              -> State LowerState ()
lowerFunction sks fsk = do
  retSid <- getSid
  let retState = PState retSid (mkPSLabels fsk) Return
      thisFinfo = FunctionInfo
        { fiEntry = Nothing
        , fiRetPad = PState (retSid + 1) (mkPSLabels fsk) Return
        , fiThrow = PState (retSid + 2) (mkPSLabels fsk) ThrowObs
        , fiSkeleton = fsk
        }
  modify (\ls -> ls { lsFinfo = M.insert (skName fsk) thisFinfo (lsFinfo ls)
                    , lsSid = retSid + 3
                    })

  let addEntry :: PredLinker
      addEntry es = modify
        (\ls -> ls { lsFinfo = M.adjust
                     (\tfinfo -> tfinfo { fiEntry = Just $ mergeDts es (fiEntry tfinfo) })
                     (skName fsk) (lsFinfo ls)
                   })

  (linkPred, _) <- lowerBlock sks thisFinfo addEntry (skStmts fsk)

  insertShift retSid (psAction retState, Det $ fiRetPad thisFinfo)
  linkPred $ Det retState

lowerStatement :: Map Text FunctionSkeleton
               -> FunctionInfo
               -> PredLinker
               -> Statement
               -> State LowerState (PredLinker, EntryTarget)
lowerStatement _ thisFinfo linkPred (Assignment lhs rhs) = do
  assSid <- getSidInc
  let assState = PState assSid (mkPSLabels $ fiSkeleton thisFinfo) (Assign lhs rhs)
      thisTarget = Det assState
  linkPred thisTarget
  insertPush assSid (psAction assState, thisTarget)
  return (\succStates -> addPops (assSid, assSid) NoRet succStates, Known thisTarget)

lowerStatement _ _ _ (Nondeterministic _) =
  error "Nondeterministic assignments not allowed in probabilistic programs."

lowerStatement _ thisFinfo linkPred (Categorical lhs exprs probs) = do
  catSid <- getSidInc
  let catState = PState catSid (mkPSLabels $ fiSkeleton thisFinfo) (Cat lhs exprs probs)
      thisTarget = Det catState
  linkPred thisTarget
  insertPush catSid (psAction catState, thisTarget)
  return (\succStates -> addPops (catSid, catSid) NoRet succStates, Known thisTarget)

lowerStatement _ thisFinfo linkPred (Uniform lhs lower upper) = do
  unifSid <- getSidInc
  let unifState = PState unifSid (mkPSLabels $ fiSkeleton thisFinfo) (Unif lhs lower upper)
      thisTarget = Det unifState
  linkPred thisTarget
  insertPush unifSid (psAction unifState, thisTarget)
  return (\succStates -> addPops (unifSid, unifSid) NoRet succStates, Known thisTarget)

lowerStatement sks thisFinfo linkPred (Call fname args) = do
  callSid <- getSidInc
  let calleeSk = sks M.! fname
      callState = PState callSid (mkPSLabels calleeSk) (CallOp fname (skParams calleeSk) args)
  notLowered <- M.notMember fname . lsFinfo <$> get
  when notLowered $ lowerFunction sks calleeSk

  calleeFinfo <- (M.! fname) . lsFinfo <$> get
  insertPush callSid (psAction callState, EntryStates fname)
  -- Since this is not a query call, we unwind it and propagate the observation
  insertPop (psId $ fiThrow calleeFinfo, callSid) (RetObs, Det $ fiThrow thisFinfo)

  let thisTarget = Det callState
  linkPred thisTarget

  return ( \succStates -> addPops (psId $ fiRetPad calleeFinfo, callSid)
                          (RetInfo (skParams calleeSk) args)
                          succStates
         , Known thisTarget
         )

lowerStatement sks thisFinfo linkPred0 (Query fname args) = do
  let fsk = fiSkeleton thisFinfo
  qrySid <- getSidInc
  let qryState = PState qrySid (mkPSLabels fsk) StartQuery
      thisTarget = Det qryState
  linkPred0 thisTarget

  -- Prepare call
  callSid <- getSidInc
  let calleeSk = sks M.! fname
      callState = PState callSid (mkPSLabels calleeSk) (CallOp fname (skParams calleeSk) args)
  -- Link query to call
  insertPush qrySid (psAction qryState, Det callState)

  -- Link call to callee
  notLowered <- M.notMember fname . lsFinfo <$> get
  when notLowered $ lowerFunction sks calleeSk
  calleeFinfo <- (M.! fname) . lsFinfo <$> get
  insertPush callSid (psAction callState, EntryStates fname)

  -- An observation was raised
  obsSid <- getSidInc
  let obsState = PState obsSid (mkPSLabels fsk) ThrowObs
  -- We restore the state before the call, without returning parameters
  insertPop (psId $ fiThrow calleeFinfo, callSid) (RetObs, Det obsState)
  -- We need to restart the query
  insertPush obsSid (psAction obsState, Det obsState)
  -- Here we don't respect the condition on pops to save one state
  insertPop (obsSid, obsSid) (NoRet, Det callState)

  -- Add dummy return to exit query block
  retSid <- getSidInc
  -- It's part of the callee because we restore the caller's state afterwards
  -- TODO: can we restore the caller's state in the pop before the shift?
  let retState = PState retSid (mkPSLabels calleeSk) Return
  -- If the query returns normally, link it to the dummy ret
  insertPop (psId $ fiRetPad calleeFinfo, callSid) (NoRet, Det retState)
  -- Shift the qry
  insertShift retSid (psAction retState, Det retState)

  return ( \succStates -> addPops (retSid, qrySid)
                          (RetInfo (skParams calleeSk) args) succStates
                          -- Restore variables from before the query
         , Known thisTarget
         )

lowerStatement _ _ _ (TryCatch _ _) =
  error "Try-catch not allowed in probabilistic programs."

lowerStatement sks thisFinfo linkPred0 (IfThenElse (Just bexp) thenBlock elseBlock) = do
  let linkPred0Then succStates = linkPred0 (combGuards bexp succStates)
      linkPred0Else succStates = linkPred0 (combGuards (Not bexp) succStates)
  (linkPred1, thenTarget) <- lowerBlock sks thisFinfo linkPred0Then thenBlock
  (linkPred2, elseTarget) <- lowerBlock sks thisFinfo linkPred0Else elseBlock
  let compTargets tt te = mergeDts (combGuards bexp tt) (Just $ combGuards (Not bexp) te)
  return ( \succStates -> linkPred1 succStates >> linkPred2 succStates
         , case thenTarget of
             Known tt -> case elseTarget of
               Known te -> Known $ compTargets tt te
               Thunk te -> Thunk $ \st -> compTargets tt (te st)
             Thunk tt -> case elseTarget of
               Known te -> Thunk $ \st -> compTargets (tt st) te
               Thunk te -> Thunk $ \st -> compTargets (tt st) (te st)
         )
lowerStatement _ _ _ (IfThenElse Nothing _ _) =
  error "Nondeterministic guards not allowed in probabilistic programs."

lowerStatement sks thisFinfo linkPred0 (While (Just bexp) body) = do
  let linkPred1 succStates = linkPred0 $ combGuards bexp succStates
  (linkBody, bodyEntry) <- lowerBlock sks thisFinfo linkPred1 body
  let bodyTarget = case bodyEntry of
        Known t -> combGuards bexp t
        Thunk _ -> error "Loops with empty body execution paths are not allowed."
  linkBody bodyTarget
  return ( \succStates ->
             let exitEdges = combGuards (Not bexp) succStates
             in linkPred0 exitEdges >> linkBody exitEdges
         , Thunk $ \st -> mergeDts bodyTarget (Just $ combGuards (Not bexp) st)
         )
lowerStatement _ _ _ (While Nothing _) =
  error "Nondeterministic guards not allowed in probabilistic programs."

lowerStatement _ thisFinfo linkPred (Throw (Just guard)) =
  let thisTarget = Guard [(Not $ guard, fiThrow thisFinfo)]
  in linkPred thisTarget >>
     return (\succStates -> linkPred $ combGuards guard succStates, Known thisTarget)
lowerStatement _ _ _ (Throw Nothing) =
  error "Exceptions not allowed in probabilistic programs."

combGuards :: Expr -> DeltaTarget -> DeltaTarget
combGuards bexp1 (Det ps) = Guard [(bexp1, ps)]
combGuards bexp1 (Guard targets) =
  Guard $ map (\(bexp2, ps) -> (bexp1 `And` bexp2, ps)) targets
combGuards _ _ = error "DeltaTarget mismatch."

lowerBlock :: Map Text FunctionSkeleton
           -> FunctionInfo
           -> PredLinker
           -> [Statement]
           -> State LowerState (PredLinker, EntryTarget)
lowerBlock _ _ linkPred [] = return (linkPred, Thunk id)
lowerBlock sks thisFinfo linkPred0 block = foldM foldBlock (linkPred0, Thunk id) block
  where foldBlock (linkPred1, entryTarget) stmt = do
          (linkPred2, newEt) <- lowerStatement sks thisFinfo linkPred1 stmt
          let resEt = case entryTarget of
                Known _ -> entryTarget
                Thunk et -> case newEt of
                  Known rt -> Known $ et rt
                  Thunk rt -> Thunk $ et . rt
          return (linkPred2, resEt)


-- Conversion of the Extended pOPA to a plain pOPA
programToPopa :: Program -> Set (Prop ExprProp)
              -> ( PropConv ExprProp
                 , Popa VarState APType
                 )
programToPopa prog additionalProps =
  let (ini, lowerState) = {-DBG.traceShowId $-} sksToExtendedOpa (pSks prog)

      allProps = foldr S.insert additionalProps miniProbSls
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
     , Popa { popaAlphabet = encodeAlphabet pconv miniProbAlphabet
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
                -> Map Word (Action, DeltaTarget)
                -> E.BitEncoding
                -> VarState
                -> RichDistr VarState Label
applyDeltaInput pconv allProps gvii localsInfo delta bitenc (sid, svval) =
  case M.lookup sid delta of
    Nothing -> error $ "Unexpected dead state " ++ show sid
    Just (act, dt) -> computeDsts bitenc pconv allProps gvii localsInfo svval act dt

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
    Nothing -> error $ "Unexpected dead state" ++ (show (sid, stackSid))
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
    Just (RetObs, dt) -> computeDsts bitenc pconv allProps gvii localsInfo stackVval Return dt
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
computeDsts bitenc pconv allProps gvii localsInfo oldVval act dt =
  let newDsts = case dt of
        Det ps -> map (\(newVval, prob) -> ((ps, newVval), prob)) $ newVvals cvval
        Guard dsts -> concatMap (composeDst cvval) dsts
        EntryStates _ -> error "Unexpected EntryStates"
  in map (\((ps, vval0), prob) ->
            let vval1 = prepareForCall (psAction ps) vval0
            in ( (psId ps, vval0)
               , pStateToLabel bitenc pconv allProps gvii localsInfo ps vval1
               , prob
               )
         ) -- Calls must be evaluated immediately in the label,
           -- but we leave the rest of the state unchanged so it gets pushed.
           -- Other actions are evaluated in the next state
     newDsts
  where cvval = case act of
          CallOp _ _ _ -> prepareForCall act oldVval
          _ -> oldVval
        composeDst vval (g, dst)
          | toBool $ evalExpr gvii vval g =
              map (\(newVval, prob) -> ((dst, newVval), prob)) $ newVvals vval
          | otherwise = []
        newVvals vval = case act of
          Assign (LScalar lhs) rhs -> [(scalarAssign gvii vval lhs $ evalExpr gvii vval rhs, 1)]
          Assign (LArray var idxExpr) rhs ->
            [(arrayAssign gvii vval var idxExpr $ evalExpr gvii vval rhs, 1)]
          Unif (LScalar lhs) lower upper -> evalUnif vval (scalarAssign gvii vval lhs) lower upper
          Unif (LArray var idxExpr) lower upper ->
            evalUnif vval (arrayAssign gvii vval var idxExpr) lower upper
          Cat (LScalar lhs) exprs probs -> evalCat vval (scalarAssign gvii vval lhs) exprs probs
          Cat (LArray var idxExpr) exprs probs ->
            evalCat vval (arrayAssign gvii vval var idxExpr) exprs probs
          _ -> [(vval, 1)]

        evalUnif vval assThunk lower upper =
          let lval = evalExpr gvii vval lower
              uval = evalExpr gvii vval upper
              (l, u) = (B.nat lval, B.nat uval)
              n = u - l + 1
          in zip (map assThunk [lval .. uval]) (repeat $ 1 % n)

        evalCat vval assThunk exprs probs =
          let assVvals = map (assThunk . evalExpr gvii vval) exprs
              probVals = map (\(n, d) -> B.nat (evalExpr gvii vval n)
                                         % B.nat (evalExpr gvii vval d)) probs
              allProbVals = probVals ++ [1 - sum probVals]
          in zip assVvals allProbVals

        prepareForCall :: Action -> VarValuation -> VarValuation
        prepareForCall (CallOp fname fargs aargs) svval =
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
        prepareForCall _ svval = svval

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
actionStruct ac = Prop . TextProp . T.pack $ case ac of
  Assign {}  -> "stm"
  Cat {}     -> "stm"
  Unif {}    -> "stm"
  CallOp {}  -> "call"
  Return     -> "ret"
  StartQuery -> "qry"
  ThrowObs   -> "obs"
  Stutter    -> "stm"


-- OPM
miniProbSls :: [Prop ExprProp]
miniProbSls = map (Prop . TextProp . T.pack) ["call", "ret", "qry", "obs", "stm"]

miniProbPrecRel :: [StructPrecRel ExprProp]
miniProbPrecRel =
  map (\(sl1, sl2, pr) ->
         (Prop . TextProp . T.pack $ sl1, Prop . TextProp . T.pack $ sl2, pr)) precs
  ++ map (\p -> (p, End, Take)) miniProbSls
  where precs = [ ("call", "call", Yield)
                , ("call", "ret",  Equal)
                , ("call", "qry",  Yield)
                , ("call", "obs",  Take)
                , ("call", "stm",  Yield)
                , ("ret",  "call", Take)
                , ("ret",  "ret",  Take)
                , ("ret",  "qry",  Take)
                , ("ret",  "obs",  Take)
                , ("ret",  "stm",  Take)
                , ("qry",  "call", Yield)
                , ("qry",  "ret",  Equal)
                , ("qry",  "qry",  Yield)
                , ("qry",  "obs",  Yield)
                , ("qry",  "stm",  Yield)
                , ("obs",  "call", Take)
                , ("obs",  "ret",  Take)
                , ("obs",  "qry",  Take)
                , ("obs",  "obs",  Take)
                , ("obs",  "stm",  Take)
                , ("stm",  "call", Take)
                , ("stm",  "ret",  Take)
                , ("stm",  "qry",  Take)
                , ("stm",  "obs",  Take)
                , ("stm",  "stm",  Take)
                ]

miniProbAlphabet :: Alphabet ExprProp
miniProbAlphabet = (miniProbSls, miniProbPrecRel)

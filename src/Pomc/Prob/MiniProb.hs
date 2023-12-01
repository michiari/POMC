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
                          , miniProbAlphabet
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
import Data.Maybe (isNothing, fromJust)
import Data.Vector (Vector)
import qualified Data.Vector as V
import Control.Monad.State.Lazy (State, runState, get, gets, modify, when)

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

insertPush :: Word -> (PState, DeltaTarget) -> State LowerState ()
insertPush key val =
  modify (\ls -> ls { lsDPush = M.insert key val $ lsDPush ls })

insertShift :: Word -> (PState, DeltaTarget) -> State LowerState ()
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
  insertPush 0 (firstCall, EntryStates firstFname)

  let stutter = PState 1 (T.empty, []) Stutter
  insertPop (psId $ fiRetPad firstFinfo, 0) (RetInfo [] [], Det stutter)

  -- Add stuttering transitions
  insertPush 1 (stutter, Det stutter)
  insertPop (1, 1) (NoRet, Det stutter)

  let uncaughtObs = PState 2 (T.empty, []) ThrowObs
  insertPop (psId $ fiThrow firstFinfo, 0) (NoRet, Det uncaughtObs)
  insertPush 2 (uncaughtObs, Det stutter)
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

mergeDts :: DeltaTarget -> Maybe DeltaTarget -> Maybe DeltaTarget
mergeDts dt Nothing = Just dt
mergeDts (Guard news) (Just (Guard olds)) = Just . Guard $ olds ++ news
mergeDts _ _ = error "DeltaTarget mismatch."

dInsert :: (Ord k) => k -> l -> DeltaTarget
        -> Map k (l, DeltaTarget) -> Map k (l, DeltaTarget)
dInsert key label dt delta =
  M.alter (fmap (\ndt -> (label, ndt)) . mergeDts dt . fmap snd) key delta

addPops :: (Word, Word) -> RetInfo -> DeltaTarget -> State LowerState ()
addPops key label dt =
  modify (\ls -> ls { lsDPop = dInsert key label dt $ lsDPop ls })

addPushes :: Word -> PState -> DeltaTarget -> State LowerState ()
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
        , fiExcPad = PState (retSid + 3) (mkPSLabels fsk) ThrowObs
        , fiSkeleton = fsk
        }
  modify (\ls -> ls { lsFinfo = M.insert (skName fsk) thisFinfo (lsFinfo ls)
                    , lsSid = retSid + 4
                    })

  let addEntry :: PredLinker
      addEntry es = modify
        (\ls -> ls { lsFinfo = M.adjust
                     (\tfinfo -> tfinfo { fiEntry = mergeDts es (fiEntry tfinfo) })
                     (skName fsk) (lsFinfo ls)
                   })

  (linkPred, _) <- lowerBlock sks thisFinfo addEntry (skStmts fsk)

  insertShift retSid (retState, Det $ fiRetPad thisFinfo)
  insertShift (psId $ fiThrow thisFinfo) (fiThrow thisFinfo, Det $ fiExcPad thisFinfo)
  linkPred $ Det retState

lowerStatement :: Map Text FunctionSkeleton
               -> FunctionInfo
               -> PredLinker
               -> Statement
               -> State LowerState (PredLinker, DeltaTarget)
lowerStatement _ thisFinfo linkPred (Assignment lhs rhs) = do
  assSid <- getSidInc
  let assState = PState assSid (mkPSLabels $ fiSkeleton thisFinfo) (Assign lhs rhs)
      thisTarget = Det assState
  linkPred thisTarget
  insertPush assSid (assState, thisTarget)
  return (\succStates -> addPops (assSid, assSid) NoRet succStates, thisTarget)

lowerStatement _ _ _ (Nondeterministic _) =
  error "Nondeterministic assignments not allowed in probabilistic programs."

lowerStatement _ thisFinfo linkPred (Categorical lhs exprs probs) = do
  catSid <- getSidInc
  let catState = PState catSid (mkPSLabels $ fiSkeleton thisFinfo) (Cat lhs exprs probs)
      thisTarget = Det catState
  linkPred thisTarget
  insertPush catSid (catState, thisTarget)
  return (\succStates -> addPops (catSid, catSid) NoRet succStates, thisTarget)

lowerStatement sks thisFinfo linkPred (Call fname args) = do
  callSid <- getSidInc
  let calleeSk = sks M.! fname
      callState = PState callSid (mkPSLabels calleeSk) (CallOp fname (skParams calleeSk) args)
  notLowered <- M.notMember fname . lsFinfo <$> get
  when notLowered $ lowerFunction sks calleeSk

  calleeFinfo <- (M.! fname) . lsFinfo <$> get
  insertPush callSid (callState, EntryStates fname)
  insertPop (psId $ fiThrow calleeFinfo, callSid) (NoRet, Det $ fiThrow thisFinfo)

  let thisTarget = Det callState
  linkPred thisTarget

  return ( \succStates -> addPops (psId $ fiRetPad calleeFinfo, callSid)
                          (RetInfo (skParams calleeSk) args)
                          succStates
         , thisTarget
         )

lowerStatement sks thisFinfo linkPred0 (TryCatch body []) = do
  let fsk = fiSkeleton thisFinfo
  qrySid <- getSidInc
  let qryState = PState qrySid (mkPSLabels fsk) StartQuery
      thisTarget = Det qryState
  linkPred0 thisTarget

  let linkQuery successorStates = addPushes qrySid qryState successorStates
  (linkBody, bodyTarget) <- lowerBlock sks thisFinfo linkQuery body

  -- add dummy return to exit query block
  retSid <- getSidInc
  let retState = PState retSid (mkPSLabels fsk) Return

  linkBody (Det retState)
  insertShift retSid (retState, Det retState)
  let linkNormalExit succStates = addPops (retSid, qrySid) NoRet succStates

  -- if an obs is thrown, we restart the body
  insertPop (psId $ fiExcPad thisFinfo, qrySid) (NoRet, bodyTarget)

  return (linkNormalExit, thisTarget)
lowerStatement _ _ _ (TryCatch _ _) =
  error "Try-catch not allowed in probabilistic programs."

lowerStatement sks thisFinfo linkPred0 (IfThenElse (Just bexp) thenBlock elseBlock) = do
  let linkPred0Then succStates = linkPred0 (combGuards bexp succStates)
      linkPred0Else succStates = linkPred0 (combGuards (Not bexp) succStates)
  (linkPred1, thenTarget) <- lowerBlock sks thisFinfo linkPred0Then thenBlock
  (linkPred2, elseTarget) <- lowerBlock sks thisFinfo linkPred0Else elseBlock
  return ( \succStates -> linkPred1 succStates >> linkPred2 succStates
         , fromJust $ mergeDts (combGuards bexp thenTarget)
           (Just $ combGuards (Not bexp) elseTarget)
         )
lowerStatement _ _ _ (IfThenElse Nothing _ _) =
  error "Nondeterministic guards not allowed in probabilistic programs."

lowerStatement sks thisFinfo linkPred0 (While (Just bexp) body) = do
  let linkPred1 succStates = linkPred0 $ combGuards bexp succStates
  (linkBody, bodyTarget) <- lowerBlock sks thisFinfo linkPred1 body
  linkBody $ combGuards bexp bodyTarget
  return ( \succStates ->
             let exitEdges = combGuards (Not bexp) succStates
             in linkPred0 exitEdges >> linkBody exitEdges
         , bodyTarget
         )
lowerStatement _ _ _ (While Nothing _) =
  error "Nondeterministic guards not allowed in probabilistic programs."

lowerStatement _ thisFinfo linkPred (Throw (Just guard)) =
  let thisTarget = Guard [(Not $ guard, fiThrow thisFinfo)]
  in linkPred thisTarget >>
     return (\succStates -> linkPred $ combGuards guard succStates, thisTarget)
lowerStatement _ _ _ (Throw Nothing) =
  error "Exceptions not allowed in probabilistic programs."

combGuards :: Expr -> DeltaTarget -> DeltaTarget
combGuards bexp1 (Det ps) = Guard [(bexp1, ps)]
combGuards bexp1 (Guard targets) =
  Guard $ map (\(bexp2, ps) -> ((bexp1 `And` bexp2), ps)) targets
combGuards _ _ = error "DeltaTarget mismatch."

lowerBlock :: Map Text FunctionSkeleton
           -> FunctionInfo
           -> PredLinker
           -> [Statement]
           -> State LowerState (PredLinker, DeltaTarget)
lowerBlock _ _ linkPred [] = return (linkPred, Guard [])
lowerBlock sks thisFinfo linkPred0 (first : rest) = do
  (linkPred1, initStates) <- lowerStatement sks thisFinfo linkPred0 first -- TODO: fix for when this can return empty initStates
  linkPred2 <- foldBlock linkPred1 rest
  return (linkPred2, initStates)
  where foldBlock linkPred1 [] = return linkPred1
        foldBlock linkPred1 (stmt : stmts) = do
          (linkPred2, _) <- lowerStatement sks thisFinfo linkPred1 stmt
          foldBlock linkPred2 stmts


-- Conversion of the Extended pOPA to a plain pOPA
programToPopa :: Bool -> Program -> Set (Prop ExprProp)
              -> ( PropConv ExprProp
                 , Popa VarState APType
                 )
programToPopa isOmega prog additionalProps =
  let (ini, lowerState) = sksToExtendedOpa (pSks prog)

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
          Cat (LScalar lhs) exprs probs -> evalCat (scalarAssign gvii vval lhs) exprs probs
          Cat (LArray var idxExpr) exprs probs ->
            evalCat (arrayAssign gvii vval var idxExpr) exprs probs
          _ -> [(vval, 1)]

        evalCat assThunk exprs probs =
          let assVvals = map (assThunk . evalExpr gvii vval) exprs
              probVals = map (\(n, d) -> B.nat (evalExpr gvii vval n)
                                         % B.nat (evalExpr gvii vval d)) probs
              allProbVals = probVals ++ [1 - sum probVals]
          in zip assVvals allProbVals

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
actionStruct ac = Prop . TextProp . T.pack $ case ac of
  Assign {}  -> "stm"
  Cat {}     -> "stm"
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

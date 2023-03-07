{-# LANGUAGE DeriveGeneric #-}

{- |
   Module      : Pomc.MiniProc
   Copyright   : 2020-2021 Michele Chiari
   License     : MIT
   Maintainer  : Michele Chiari
-}

module Pomc.MiniProc ( Program(..)
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
                     , isSigned
                     , isScalar
                     , isArray
                     , typeWidth
                     , scalarType
                     , commonType
                     , varWidth
                     , programToOpa
                     , IdType
                     , VarIdInfo(..)

                     , Guard(..)
                     , DeltaTarget(..)
                     , Action(..)
                     , InputLabel(..)
                     , LowerState(..)
                     , sksToExtendedOpa
                     , miniProcAlphabet
                     , miniProcStringAlphabet
                     ) where

import Pomc.Prop (Prop(..))
import Pomc.PropConv (APType, PropConv(..), makePropConv, encodeAlphabet)
import Pomc.Prec (Prec(..), Alphabet)
import qualified Pomc.Encoding as E
import Pomc.State (Input, State(..))

import Data.Text (Text)
import qualified Data.Text as T
import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S
import Data.Maybe (isNothing, fromJust)
import Data.BitVector (BitVector)
import qualified Data.BitVector as B
import Data.Vector (Vector)
import qualified Data.Vector as V
import GHC.Generics (Generic)
import Data.Hashable

-- import qualified Debug.Trace as DBG

-- Intermediate representation for MiniProc programs
type IdType = Int
type FunctionName = Text
data Type = UInt Int
          | SInt Int
          | UIntArray Int Int -- width size
          | SIntArray Int Int -- width size
          deriving (Show, Eq, Ord, Generic)
data Variable = Variable { varType :: Type
                         , varName :: Text
                         , varId   :: IdType
                         } deriving (Show, Eq, Ord, Generic)
type IntValue = BitVector
type ArrayValue = Vector IntValue
data Expr = Literal IntValue
          | Term Variable
          | ArrayAccess Variable Expr
          -- Boolean operations
          | Not Expr
          | And Expr Expr
          | Or Expr Expr
          -- Arithmetic operations
          | Add Expr Expr
          | Sub Expr Expr
          | Mul Expr Expr
          | UDiv Expr Expr
          | SDiv Expr Expr
          | URem Expr Expr
          | SRem Expr Expr
          -- Comparisons
          | Eq Expr Expr
          | ULt Expr Expr
          | ULeq Expr Expr
          | SLt Expr Expr
          | SLeq Expr Expr
          -- Casts
          | UExt Int Expr
          | SExt Int Expr
          | Trunc Int Expr
          deriving (Eq, Ord, Show)
data LValue = LScalar Variable | LArray Variable Expr deriving (Eq, Ord, Show)
data ActualParam = ActualVal Expr | ActualValRes Variable deriving (Eq, Ord, Show)
data Statement = Assignment LValue Expr
               | Nondeterministic LValue
               | Call FunctionName [ActualParam]
               | TryCatch [Statement] [Statement]
               | IfThenElse (Maybe Expr) [Statement] [Statement]
               | While (Maybe Expr) [Statement]
               | Throw deriving Show
data FormalParam = Value Variable | ValueResult Variable deriving (Eq, Ord, Show)
data FunctionSkeleton = FunctionSkeleton { skName    :: FunctionName
                                         , skModules :: [FunctionName]
                                         , skParams  :: [FormalParam]
                                         , skScalars :: Set Variable
                                         , skArrays  :: Set Variable
                                         , skStmts   :: [Statement]
                                         } deriving Show
data Program = Program { pGlobalScalars :: Set Variable
                       , pGlobalArrays  :: Set Variable
                       , pLocalScalars  :: Set Variable
                       , pLocalArrays   :: Set Variable
                       , pSks           :: [FunctionSkeleton]
                       } deriving Show

instance Hashable Type
instance Hashable Variable
instance Hashable B.BV where
  hashWithSalt s bv = s `hashWithSalt` B.nat bv `hashWithSalt` B.size bv
instance Hashable a => Hashable (Vector a) where
  hashWithSalt s v = V.foldl' hashWithSalt s v

isSigned :: Type -> Bool
isSigned (SInt _) = True
isSigned (SIntArray _ _) = True
isSigned _ = False

isScalar :: Type -> Bool
isScalar (UInt _) = True
isScalar (SInt _) = True
isScalar _ = False

isArray :: Type -> Bool
isArray = not . isScalar

typeWidth :: Type -> Int
typeWidth (UInt w) = w
typeWidth (SInt w) = w
typeWidth (UIntArray w _) = w
typeWidth (SIntArray w _) = w

arraySize :: Type -> Int
arraySize (UIntArray _ s) = s
arraySize (SIntArray _ s) = s
arraySize _ = error "Scalar types do not have a size."

scalarType :: Type -> Type
scalarType (UIntArray w _) = UInt w
scalarType (SIntArray w _) = SInt w
scalarType scalar = scalar

commonType :: Type -> Type -> Type
commonType (UInt w0) (UInt w1) = UInt $ max w0 w1
commonType (UInt w0) (SInt w1) = SInt $ max w0 w1
commonType (SInt w0) (UInt w1) = SInt $ max w0 w1
commonType (SInt w0) (SInt w1) = SInt $ max w0 w1
commonType _ _ = error "Arrays do not have subsuming type."

varWidth :: Variable -> Int
varWidth = typeWidth . varType

enumerateIntType :: Type -> [IntValue]
enumerateIntType ty = B.bitVecs len [(0 :: Integer)..((2 :: Integer)^len-1)]
  where len = typeWidth ty


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

      lowerState3 = lowerState2 { lsDPush = dPush'', lsDPop = dPop'', lsSid = lsSid lowerState2 + 1 }
  in (linkPred lowerState3 [(NoGuard, callSid)], linkCall)

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

lowerStatement _ lowerState thisFinfo linkPred Throw =
  (linkPred lowerState [(NoGuard, fiThrow thisFinfo)], (\ls _ -> ls))

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

        foldBlock lowerState1 linkPred1 (Throw : _) =
          let (lowerState2, linkPred2) =
                lowerStatement sks lowerState1 thisFinfo linkPred1 Throw
          in (lowerState2, linkPred2)

        foldBlock lowerState1 linkPred1 (stmt : stmts) =
          let (lowerState2, linkPred2) =
                lowerStatement sks lowerState1 thisFinfo linkPred1 stmt
          in foldBlock lowerState2 linkPred2 stmts

-- Conversion of the Extended OPA to a plain OPA

-- Data structures
data VarIdInfo = VarIdInfo { scalarIds :: IdType
                           , arrayIds  :: IdType
                           } deriving Show

isGlobal :: VarIdInfo -> Bool -> IdType -> Bool
isGlobal gvii scalar vid | scalar = vid < scalarIds gvii
                         | otherwise = vid < arrayIds gvii

getLocalIdx :: VarIdInfo -> Bool -> IdType -> Int
getLocalIdx gvii scalar vid | scalar = vid - scalarIds gvii
                            | otherwise = vid - arrayIds gvii

data VarValuation = VarValuation { vGlobalScalars :: Vector IntValue
                                 , vGlobalArrays  :: Vector ArrayValue
                                 , vLocalScalars  :: Vector IntValue
                                 , vLocalArrays   :: Vector ArrayValue
                                 } deriving (Show, Eq, Ord, Generic)
type VarState = (Word, VarValuation)

instance Hashable VarValuation

initialValuation :: (Bool -> IdType -> IdType)
                 -> Set Variable
                 -> Set Variable
                 -> (Vector IntValue, Vector ArrayValue)
initialValuation getIdx svars avars = (scalars, arrays)
  where scalars = V.replicate (S.size svars) B.nil  V.//
          map (\var -> (getIdx True $ varId var, initialScalar var)) (S.toList svars)
        arrays = V.replicate (S.size avars) V.empty V.//
          map (\var -> (getIdx False $ varId var, initialArray var)) (S.toList avars)

        initialScalar = B.zeros . varWidth
        initialArray var = V.replicate (arraySize . varType $ var) (initialScalar var)

programToOpa :: Bool -> Program -> Set (Prop Text)
             -> ( PropConv Text
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
      allVarProps = S.map (\var -> Prop $ encodeAP pconv $ varName var)
        $ S.filter (\var -> Prop (varName var) `S.member` additionalProps)
        $ pGlobalScalars prog `S.union` pLocalScalars prog
      gvii = VarIdInfo { scalarIds = S.size . pGlobalScalars $ prog
                       , arrayIds = S.size . pGlobalArrays $ prog
                       }
      localsInfo = M.insert T.empty (globalVarMap, V.empty, V.empty)
        $ M.fromList
        $ map (\sk -> let (liScalars, liArrays) =
                            initialValuation (getLocalIdx gvii) (skScalars sk) (skArrays sk)
                      in (skName sk,
                          (makeVarMap (skScalars sk) `M.union` globalVarMap, liScalars, liArrays)))
        $ pSks prog
        where globalVarMap = makeVarMap $ pGlobalScalars prog
              makeVarMap varSet = M.fromList
                $ map (\var -> (Prop $ encodeAP pconv $ varName var, varId var))
                $ filter (\var -> Prop (varName var) `S.member` additionalProps)
                $ S.toList varSet
      remapDelta delta =
        M.map (\(ilabel, States s) -> (ilabelToPropSet ilabel, ilabel, s)) delta
        where ilabelToPropSet il = S.fromList
                $ map (encodeProp pconv)
                $ filter (`S.member` allProps)
                $ map Prop $ ilStruct il : ilFunction il : ilModules il
      remappedDPush = remapDelta $ lsDPush lowerState
      remappedDShift = remapDelta $ lsDShift lowerState
      decodeDeltaInput remappedDelta bitenc q b =
        applyDeltaInput gvii allVarProps localsInfo remappedDelta q $ E.decodeInput bitenc b

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
                -> Set (Prop APType)
                -> Map FunctionName (Map (Prop APType) IdType, Vector IntValue, Vector ArrayValue)
                -> Map Word (Set (Prop APType), InputLabel, [(Guard, Word)])
                -> VarState
                -> Set (Prop APType)
                -> [VarState]
applyDeltaInput gvii allVarProps localsInfo delta (sid, svval) lbl =
  case M.lookup sid delta of
    Nothing -> []
    Just (lsProps, il, dsts) ->
      let (localPropMap, initScalars, initArrays) = localsInfo M.! ilFunction il
          callVval = prepareForCall (ilAction il) initScalars initArrays
          filterVars vid
            | isGlobal gvii True vid = toBool $ vGlobalScalars callVval V.! vid
            | otherwise = toBool $ vLocalScalars callVval V.! getLocalIdx gvii True vid
          vvalPropSet = M.keysSet $ M.filter filterVars localPropMap
      in if (vvalPropSet, lsProps) == S.partition (`S.member` allVarProps) lbl
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

scalarAssign :: VarIdInfo
             -> VarValuation
             -> Variable
             -> IntValue
             -> VarValuation
scalarAssign gvii vval var val
  | isGlobal gvii True vid = vval {
      vGlobalScalars = vGlobalScalars vval V.// [(vid, val)] }
  | otherwise = vval {
      vLocalScalars = vLocalScalars vval V.// [(getLocalIdx gvii True vid, val)] }
  where vid = varId var

arrayAssign :: VarIdInfo
            -> VarValuation
            -> Variable
            -> Expr
            -> IntValue
            -> VarValuation
arrayAssign gvii vval var idxExpr val
  | isGlobal gvii False vid = vval {
      vGlobalArrays = doAssign (vGlobalArrays vval) vid }
  | otherwise = vval {
      vLocalArrays = doAssign (vLocalArrays vval) $ getLocalIdx gvii False vid }
  where vid = varId var
        idx = fromEnum . B.nat . evalExpr gvii vval $ idxExpr
        doAssign aval varIdx =
          aval V.// [(varIdx, (aval V.! varIdx) V.// [(idx, val)])]

wholeArrayAssign :: VarIdInfo
                 -> VarValuation
                 -> Variable
                 -> VarValuation
                 -> Variable
                 -> VarValuation
wholeArrayAssign gvii dstVval dstVar srcVval srcVar
  | isGlobal gvii False dstVid = dstVval {
      vGlobalArrays = vGlobalArrays dstVval V.// [(dstVid, srcVal)] }
  | otherwise = dstVval {
      vLocalArrays = vLocalArrays dstVval V.// [(getLocalIdx gvii False dstVid, srcVal)] }
  where dstVid = varId dstVar
        srcVid = varId srcVar
        srcVal | isGlobal gvii False srcVid = vGlobalArrays srcVval V.! srcVid
               | otherwise = vLocalArrays srcVval V.! getLocalIdx gvii False srcVid

evalExpr :: VarIdInfo -> VarValuation -> Expr -> IntValue
evalExpr _ _ (Literal val) = val
evalExpr gvii vval (Term var)
  | isGlobal gvii True vid = vGlobalScalars vval V.! vid
  | otherwise = vLocalScalars vval V.! getLocalIdx gvii True vid
  where vid = varId var
evalExpr gvii vval (ArrayAccess var idxExpr) =
  arr V.! (fromEnum . B.nat . evalExpr gvii vval $ idxExpr)
  where vid = varId var
        arr | isGlobal gvii False vid = vGlobalArrays vval V.! vid
            | otherwise = vLocalArrays vval V.! getLocalIdx gvii False vid
evalExpr gvii vval (Not bexpr) = B.fromBool . not . toBool $ evalExpr gvii vval bexpr
evalExpr gvii vval (And lhs rhs) =
  B.fromBool $ (toBool $ evalExpr gvii vval lhs) && (toBool $ evalExpr gvii vval rhs)
evalExpr gvii vval (Or lhs rhs) =
  B.fromBool $ (toBool $ evalExpr gvii vval lhs) || (toBool $ evalExpr gvii vval rhs)
evalExpr gvii vval (Add lhs rhs) = evalExpr gvii vval lhs + evalExpr gvii vval rhs
evalExpr gvii vval (Sub lhs rhs) = evalExpr gvii vval lhs - evalExpr gvii vval rhs
evalExpr gvii vval (Mul lhs rhs) = evalExpr gvii vval lhs * evalExpr gvii vval rhs
evalExpr gvii vval (UDiv lhs rhs) = evalExpr gvii vval lhs `div` evalExpr gvii vval rhs
evalExpr gvii vval (SDiv lhs rhs) = evalExpr gvii vval lhs `B.sdiv` evalExpr gvii vval rhs
evalExpr gvii vval (URem lhs rhs) = evalExpr gvii vval lhs `mod` evalExpr gvii vval rhs
evalExpr gvii vval (SRem lhs rhs) = evalExpr gvii vval lhs `B.smod` evalExpr gvii vval rhs
evalExpr gvii vval (Eq lhs rhs) = B.fromBool $ evalExpr gvii vval lhs == evalExpr gvii vval rhs
evalExpr gvii vval (ULt lhs rhs) = B.fromBool $ evalExpr gvii vval lhs < evalExpr gvii vval rhs
evalExpr gvii vval (ULeq lhs rhs) = B.fromBool $ evalExpr gvii vval lhs <= evalExpr gvii vval rhs
evalExpr gvii vval (SLt lhs rhs) = B.fromBool $ evalExpr gvii vval lhs `B.slt` evalExpr gvii vval rhs
evalExpr gvii vval (SLeq lhs rhs) = B.fromBool $ evalExpr gvii vval lhs `B.sle` evalExpr gvii vval rhs
evalExpr gvii vval (UExt size op) = B.zeroExtend size $ evalExpr gvii vval op
evalExpr gvii vval (SExt size op) = B.signExtend size $ evalExpr gvii vval op
evalExpr gvii vval (Trunc size op) = evalExpr gvii vval op B.@@ (size - 1, 0)

toBool :: IntValue -> Bool
toBool v = B.nat v /= 0


-- OPM
miniProcAlphabet :: Alphabet Text
miniProcAlphabet = (miniProcSls, miniProcPrecRel) where
  (miniProcStringSls, miniProcStringPrecRel) = miniProcStringAlphabet
  miniProcSls = map (fmap T.pack) miniProcStringSls
  miniProcPrecRel =
    map (\(sl1, sl2, pr) -> (fmap T.pack sl1, fmap T.pack sl2, pr)) miniProcStringPrecRel

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

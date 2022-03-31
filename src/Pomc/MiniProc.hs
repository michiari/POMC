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

                     , DeltaTarget(..)
                     , InputLabel(..)
                     , LowerState(..)
                     , sksToExtendedOpa
                     , miniProcAlphabet
                     ) where

import Pomc.Prop (Prop(..))
import Pomc.PropConv (APType, PropConv(..), makePropConv, encodeAlphabet)
import Pomc.Prec (Prec(..), StructPrecRel, Alphabet)
import qualified Pomc.Encoding as E (BitEncoding, decodeInput)
import Pomc.State (Input)

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
          deriving Show
data LValue = LScalar Variable | LArray Variable Expr deriving Show
data Statement = Assignment LValue Expr
               | Nondeterministic LValue
               | Call FunctionName
               | TryCatch [Statement] [Statement]
               | IfThenElse (Maybe Expr) [Statement] [Statement]
               | While (Maybe Expr) [Statement]
               | Throw deriving Show
data FunctionSkeleton = FunctionSkeleton { skName :: FunctionName
                                         , skModules :: [FunctionName]
                                         , skScalars :: Set Variable
                                         , skArrays :: Set Variable
                                         , skStmts :: [Statement]
                                         } deriving Show
data Program = Program { pGlobalScalars :: Set Variable
                       , pGlobalArrays :: Set Variable
                       , pLocalScalars :: Set Variable
                       , pLocalArrays :: Set Variable
                       , pSks :: [FunctionSkeleton]
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
data Label = None | Assign LValue Expr | Guard Expr | Nondet LValue deriving Show
data DeltaTarget = EntryStates Text | States [(Label, Word)] deriving Show
data InputLabel = InputLabel { ilStruct :: Text
                             , ilFunction :: FunctionName
                             , ilModules :: [FunctionName]
                             } deriving (Eq, Ord, Show)

data FunctionInfo = FunctionInfo { fiEntry :: [(Label, Word)]
                                 , fiRetPad :: Word
                                 , fiThrow :: Word
                                 , fiExcPad :: Word
                                 , fiSkeleton :: FunctionSkeleton
                                 } deriving Show
data LowerState = LowerState { lsDPush :: Map (Word, InputLabel) DeltaTarget
                             , lsDShift :: Map (Word, InputLabel) DeltaTarget
                             , lsDPop :: Map (Word, Word) DeltaTarget
                             , lsFinfo :: Map Text FunctionInfo
                             , lsSid :: Word
                             } deriving Show

makeInputLabel :: String -> FunctionInfo -> InputLabel
makeInputLabel sl finfo = InputLabel (T.pack sl) (skName fsk) (skModules fsk)
  where fsk = fiSkeleton finfo

sksToExtendedOpa :: Bool -> [FunctionSkeleton] -> (LowerState, [Word], [Word])
sksToExtendedOpa False sks = (buildExtendedOpa sks, [0], [1]) -- Finite case
sksToExtendedOpa True sks = -- Omega case
  let lowerState = buildExtendedOpa sks
      -- Add stuttering transitions
      dPush = M.insert (1, InputLabel (T.pack "stm") T.empty [])
              (States [(None, 1)]) (lsDPush lowerState)
      dPop = M.insert (1, 1) (States [(None, 1)]) (lsDPop lowerState)
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
      dPush' = M.insert (0, InputLabel (T.pack "call") firstFname (skModules $ head sks))
               (EntryStates firstFname) (lsDPush lowerState)
      dPop' = M.insert (fiRetPad firstFinfo, 0) (States [(None, 1)]) (lsDPop lowerState)
      dPop'' = M.insert (fiThrow firstFinfo, 0) (States [(None, 2)]) dPop'
      dPush'' = M.insert (2, InputLabel (T.pack "exc") T.empty []) (States [(None, 1)]) dPush'
      dPop''' = M.insert (1, 2) (States [(None, 1)]) dPop''

      resolveTarget (EntryStates fname) =
        States . fiEntry . fromJust $ M.lookup fname (lsFinfo lowerState)
      resolveTarget x = x
      resolveAll deltaMap = M.map resolveTarget deltaMap
  in lowerState { lsDPush = resolveAll dPush''
                , lsDShift = resolveAll $ lsDShift lowerState
                , lsDPop = resolveAll dPop'''
                }

-- Thunk that links a list of states as the successors of the previous statement(s)
type PredLinker = LowerState -> [(Label, Word)] -> LowerState

dInsert :: (Ord k) => k -> [(Label, Word)] -> Map k DeltaTarget -> Map k DeltaTarget
dInsert _ [] delta = delta
dInsert key states delta =
  case M.lookup key delta of
    Nothing            -> M.insert key (States states) delta
    Just (States olds) -> M.insert key (States $ olds ++ states) delta
    _                  -> error "DeltaTarget mismatch."

lowerFunction :: Map Text FunctionSkeleton
              -> LowerState
              -> FunctionSkeleton
              -> LowerState
lowerFunction sks lowerState0 fsk =
  let sidRet = lsSid lowerState0
      thisFinfo = FunctionInfo [] (sidRet + 1) (sidRet + 2) (sidRet + 3) fsk
      lowerState1 = lowerState0 {
        lsFinfo = M.insert (skName fsk) thisFinfo (lsFinfo lowerState0)
        , lsSid = sidRet + 4
        }
      addEntry ls es =
        let tfinfo = fromJust $ M.lookup (skName fsk) (lsFinfo ls)
            finfo1 = M.insert (skName fsk) (tfinfo { fiEntry = (fiEntry tfinfo) ++ es }) (lsFinfo ls)
        in ls { lsFinfo = finfo1 }

      (lowerState2, linkPred) = lowerBlock sks lowerState1 thisFinfo addEntry (skStmts fsk)

      dShift' = M.insert (sidRet, InputLabel (T.pack "ret") (skName fsk) (skModules fsk))
                 (States [(None, fiRetPad thisFinfo)]) (lsDShift lowerState2)
      dShift'' = M.insert (fiThrow thisFinfo, InputLabel (T.pack "exc") (skName fsk) (skModules fsk))
                 (States [(None, fiExcPad thisFinfo)]) dShift'
  in linkPred (lowerState2 { lsDShift = dShift'' }) [(None, sidRet)]

lowerStatement :: Map Text FunctionSkeleton
               -> LowerState
               -> FunctionInfo
               -> PredLinker
               -> Statement
               -> (LowerState, PredLinker)
lowerStatement _ lowerState0 thisFinfo linkPred (Assignment lhs rhs) =
  let assSid = lsSid lowerState0
      lowerState1 = linkPred (lowerState0 { lsSid = assSid + 1 }) [(None, assSid)]
      dPush' = dInsert (assSid, makeInputLabel "stm" thisFinfo)
               [(Assign lhs rhs, assSid)]
               (lsDPush lowerState1)

      linkAss ls succStates =
        let dPop' = dInsert (assSid, assSid) succStates (lsDPop ls)
        in ls { lsDPop = dPop' }

  in (lowerState1 { lsDPush = dPush' }, linkAss)

lowerStatement _ lowerState0 thisFinfo linkPred (Nondeterministic lval) =
  let assSid = lsSid lowerState0
      lowerState1 = linkPred (lowerState0 { lsSid = assSid + 1 }) [(None, assSid)]
      dPush' = dInsert (assSid, makeInputLabel "stm" thisFinfo)
               [(Nondet lval, assSid)]
               (lsDPush lowerState1)

      linkAss ls succStates =
        let dPop' = dInsert (assSid, assSid) succStates (lsDPop ls)
        in ls { lsDPop = dPop' }

  in (lowerState1 { lsDPush = dPush' }, linkAss)

lowerStatement sks lowerState0 thisFinfo linkPred (Call fname) =
  let calleeSk = fromJust $ M.lookup fname sks
      callSid = lsSid lowerState0
      calleeFinfo0 = M.lookup fname $ lsFinfo lowerState0
      lowerState1 = lowerState0 { lsSid = callSid + 1 }
      lowerState2 = if isNothing calleeFinfo0
                    then lowerFunction sks lowerState1 calleeSk
                    else lowerState1
      calleeFinfo1 = fromJust $ M.lookup fname (lsFinfo lowerState2)
      dPush'' = M.insert (callSid, InputLabel (T.pack "call") fname (skModules calleeSk))
                (EntryStates fname) (lsDPush lowerState2)
      dPop'' = M.insert (fiThrow calleeFinfo1, callSid)
               (States [(None, fiThrow thisFinfo)]) (lsDPop lowerState2)

      linkCall lowerState successorStates =
          let dPop' = dInsert (fiRetPad calleeFinfo1, callSid) successorStates (lsDPop lowerState)
          in lowerState { lsDPop = dPop' }

      lowerState3 = lowerState2 { lsDPush = dPush'', lsDPop = dPop'', lsSid = lsSid lowerState2 + 1 }
  in (linkPred lowerState3 [(None, callSid)], linkCall)

lowerStatement sks ls0 thisFinfo linkPred0 (TryCatch try catch) =
  let hanSid = lsSid ls0
      dummySid0 = hanSid + 1
      dummySid1 = dummySid0 + 1
      ls1 = linkPred0 (ls0 { lsSid = dummySid1 + 1 }) [(None, hanSid)]

      linkHandler lowerState successorStates =
        let dPushH = dInsert (hanSid, makeInputLabel "han" thisFinfo)
                     successorStates (lsDPush lowerState)
        in lowerState { lsDPush = dPushH }

      (ls2, linkPredTry) = lowerBlock sks ls1 thisFinfo linkHandler try
      -- add dummy exc to exit try block
      ls3 = linkPredTry ls2 [(None, dummySid0)]
      dShift' = M.insert (dummySid0, makeInputLabel "exc" thisFinfo)
                (States [(None, dummySid1)]) (lsDShift ls3)
      ls4 = ls3 { lsDShift = dShift' }

      linkTry lowerState successorStates =
        let dPopD = dInsert (dummySid1, hanSid) successorStates (lsDPop lowerState)
        in lowerState { lsDPop = dPopD }

      linkCatch lowerState successorStates =
        let dPopC = dInsert (fiExcPad thisFinfo, hanSid) successorStates (lsDPop lowerState)
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
  (linkPred lowerState [(None, fiThrow thisFinfo)], (\ls _ -> ls))

combGuards :: Expr -> Label -> Label
combGuards bexp1 None = Guard bexp1
combGuards bexp1 (Guard bexp2) = Guard (bexp1 `And` bexp2)
combGuards _ (Assign _ _) = error "Cannot combine Guard with Assignment label."
combGuards _ (Nondet _) = error "Cannot combine Guard with Nondet label."

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

      allProps = foldr S.insert additionalProps miniProcSls
      pconv = makePropConv $ S.toList allProps
      varPropMap = foldl genPropMap M.empty
        $ (M.keys $ lsDPush lowerState) ++ (M.keys $ lsDShift lowerState)
        where funLocals = M.fromList
                $ map (\sk -> (skName sk,
                               makeVarMap (skScalars sk) `M.union` globalVarMap))
                $ pSks prog
              globalVarMap = makeVarMap $ pGlobalScalars prog
              makeVarMap varSet = M.fromList
                $ map (\var -> (Prop $ encodeAP pconv $ varName var, varId var))
                $ filter (\var -> Prop (varName var) `S.member` additionalProps)
                $ S.toList varSet
              genPropMap pm (sid, il) | T.null $ ilFunction il = M.insert sid globalVarMap pm
                                      | otherwise = M.insert sid (funLocals M.! ilFunction il) pm
      initLocals = foldl genLocals M.empty $ M.keys $ lsDPush lowerState
        where funInitLocals = M.fromList
                $ map (\sk -> (skName sk,
                               initialValuation (getLocalIdx gvii) (skScalars sk) (skArrays sk)))
                $ pSks prog
              genLocals ils (sid, a)
                | ilStruct a == T.pack "call" = M.insert sid (funInitLocals M.! ilFunction a) ils
                | otherwise = ils
      gvii = VarIdInfo { scalarIds = S.size . pGlobalScalars $ prog
                       , arrayIds = S.size . pGlobalArrays $ prog
                       }
      decodeDeltaInput il delta bitenc q b =
        applyDeltaInput gvii varPropMap il delta q $ E.decodeInput bitenc b

      remapProps = M.mapKeysWith (\(States s1) (States s2) -> States $ s1 ++ s2)
                    (\(sid, ilabel) ->
                       (sid, S.fromList $ map (encodeProp pconv)
                             $ filter (`S.member` allProps) (iLabelToList ilabel)))
                   where iLabelToList il = map Prop $ ilStruct il : ilFunction il : ilModules il
  in ( pconv
     , encodeAlphabet pconv miniProcAlphabet
     , eInitials
     , if isOmega then const True else eIsFinal
     , decodeDeltaInput initLocals $ remapProps $ lsDPush lowerState
     , decodeDeltaInput M.empty $ remapProps $ lsDShift lowerState
     , applyDeltaPop (M.keysSet initLocals) gvii $ lsDPop lowerState
     )

applyDeltaInput :: VarIdInfo
                -- map between sid and map between variable props and their ids,
                -- only in the scope of the sids' function
                -> Map Word (Map (Prop APType) IdType)
                -- map between call sid and initial values of its function-local vars
                -> Map Word (Vector IntValue, Vector ArrayValue)
                -> Map (Word, Set (Prop APType)) DeltaTarget
                -> VarState
                -> Set (Prop APType)
                -> [VarState]
applyDeltaInput gvii varPropMap initLocals delta (sid, svval) lbl =
  let callVval = case M.lookup sid initLocals of
                   Nothing -> svval
                   Just (lscalars, larrays) -> svval { vLocalScalars = lscalars
                                                     , vLocalArrays = larrays
                                                     }
      localPropMap = case M.lookup sid varPropMap of
                       Nothing -> M.empty
                       Just lpm -> lpm
      filterVars vid
        | isGlobal gvii True vid = toBool $ vGlobalScalars callVval V.! vid
        | otherwise = toBool $ vLocalScalars callVval V.! getLocalIdx gvii True vid
      vvalPropSet = M.keysSet $ M.filter filterVars localPropMap
      (varProps, lsProps) = S.partition (`M.member` localPropMap) lbl
  in if varProps == vvalPropSet
     then case M.lookup (sid, lsProps) delta of
            Nothing              -> []
            Just (States dsts)   -> concatMap (computeDst gvii callVval) dsts
            Just (EntryStates _) -> error "Expected States, got EntryStates."
     else []

applyDeltaPop :: Set Word
              -> VarIdInfo
              -> Map (Word, Word) DeltaTarget
              -> VarState
              -> VarState
              -> [VarState]
applyDeltaPop callSites gvii delta (sid, svval) (stackSid, stackVval) =
  case M.lookup (sid, stackSid) delta of
    Nothing              -> []
    Just (States dsts)   -> concatMap (computeDst gvii newVval) dsts
    Just (EntryStates _) -> error "Expected States, got EntryStates."
  where newVval | stackSid `S.member` callSites =
                  svval { vLocalScalars = vLocalScalars stackVval
                        , vLocalArrays = vLocalArrays stackVval
                        }
                | otherwise = svval

computeDst :: VarIdInfo -> VarValuation -> (Label, Word) -> [VarState]
computeDst _ vval (None, dst) = [(dst, vval)]
computeDst gvii vval (Assign (LScalar lhs) rhs, dst) =
  [(dst, scalarAssign gvii vval lhs $ evalExpr gvii vval rhs)]
computeDst gvii vval (Assign (LArray var idxExpr) rhs, dst) =
  [(dst, arrayAssign gvii vval var idxExpr $ evalExpr gvii vval rhs)]
computeDst gvii vval (Guard g, dst)
  | toBool $ evalExpr gvii vval g = [(dst, vval)]
  | otherwise = []
computeDst gvii vval (Nondet (LScalar var), dst) =
  map (\val -> (dst, scalarAssign gvii vval var val))
  $ enumerateIntType (varType var)
computeDst gvii vval (Nondet (LArray var idxExpr), dst) =
  map (\val -> (dst, arrayAssign gvii vval var idxExpr val))
  $ enumerateIntType (varType var)

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
miniProcSls :: [Prop Text]
miniProcSls = map (Prop . T.pack) ["call", "ret", "han", "exc", "stm"]

miniProcPrecRel :: [StructPrecRel Text]
miniProcPrecRel = map (\(sl1, sl2, pr) -> (Prop . T.pack $ sl1, Prop . T.pack $ sl2, pr)) precs
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

miniProcAlphabet :: Alphabet Text
miniProcAlphabet = (miniProcSls, miniProcPrecRel)

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
                     , typeWidth
                     , scalarType
                     , commonType
                     , varWidth
                     , programToOpa

                     , DeltaTarget(..)
                     , LowerState(..)
                     , sksToExtendedOpa
                     , miniProcSls
                     , miniProcPrecRel
                     ) where

import Pomc.Prop (Prop(..))
import Pomc.PropConv (APType, PropConv(..), makePropConv, encodeStructPrecRel)
import Pomc.Prec (Prec(..), StructPrecRel)
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
type FunctionName = Text
data Type = UInt Int
          | SInt Int
          | UIntArray Int Int -- width size
          | SIntArray Int Int -- width size
          deriving (Show, Eq, Ord, Generic)
data Variable = Variable { varType :: Type
                         , varName :: Text
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
                                         , skStmts :: [Statement]
                                         } deriving Show
data Program = Program { pVars :: Set Variable
                       , pSks :: [FunctionSkeleton]
                       } deriving Show

instance Hashable Type
instance Hashable Variable
-- TODO: see if there's a better way of doing this
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

data FunctionInfo = FunctionInfo { fiEntry :: [(Label, Word)]
                                 , fiRetPad :: Word
                                 , fiThrow :: Word
                                 , fiExcPad :: Word
                                 } deriving Show
data LowerState = LowerState { lsDPush :: Map (Word, Set (Prop Text)) DeltaTarget
                             , lsDShift :: Map (Word, Set (Prop Text)) DeltaTarget
                             , lsDPop :: Map (Word, Word) DeltaTarget
                             , lsFinfo :: Map Text FunctionInfo
                             , lsSid :: Word
                             } deriving Show

sksToExtendedOpa :: Bool -> [FunctionSkeleton] -> (LowerState, [Word], [Word])
sksToExtendedOpa False sks = (buildExtendedOpa sks, [0], [1]) -- Finite case
sksToExtendedOpa True sks = -- Omega case
  let lowerState = buildExtendedOpa sks
      -- Add stuttering transitions
      dPush = M.insert (1, makeInputSet [T.pack "stm"]) (States [(None, 1)]) (lsDPush lowerState)
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
      dPush' = M.insert (0, makeInputSet $ [T.pack "call", firstFname] ++ (skModules $ head sks))
               (EntryStates firstFname) (lsDPush lowerState)
      dPop' = M.insert (fiRetPad firstFinfo, 0) (States [(None, 1)]) (lsDPop lowerState)
      dPop'' = M.insert (fiThrow firstFinfo, 0) (States [(None, 2)]) dPop'
      dPush'' = M.insert (2, makeInputSet [T.pack "exc"]) (States [(None, 1)]) dPush'
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

makeInputSet :: (Ord a) => [a] -> Set (Prop a)
makeInputSet ilst = S.fromList $ map Prop ilst

lowerFunction :: Map Text FunctionSkeleton
              -> LowerState
              -> FunctionSkeleton
              -> LowerState
lowerFunction sks lowerState0 fsk =
  let sidRet = lsSid lowerState0
      thisFinfo = FunctionInfo [] (sidRet + 1) (sidRet + 2) (sidRet + 3)
      lowerState1 = lowerState0 {
        lsFinfo = M.insert (skName fsk) thisFinfo (lsFinfo lowerState0)
        , lsSid = sidRet + 4
        }
      addEntry ls es =
        let tfinfo = fromJust $ M.lookup (skName fsk) (lsFinfo ls)
            finfo1 = M.insert (skName fsk) (tfinfo { fiEntry = (fiEntry tfinfo) ++ es }) (lsFinfo ls)
        in ls { lsFinfo = finfo1 }

      (lowerState2, linkPred) = lowerBlock sks lowerState1 thisFinfo addEntry (skStmts fsk)

      dShift' = M.insert (sidRet, makeInputSet $ [T.pack "ret", skName fsk] ++ skModules fsk)
                 (States [(None, fiRetPad thisFinfo)]) (lsDShift lowerState2)
      dShift'' = M.insert (fiThrow thisFinfo, makeInputSet [T.pack "exc"])
                 (States [(None, fiExcPad thisFinfo)]) dShift'
  in linkPred (lowerState2 { lsDShift = dShift'' }) [(None, sidRet)]

lowerStatement :: Map Text FunctionSkeleton
               -> LowerState
               -> FunctionInfo
               -> PredLinker
               -> Statement
               -> (LowerState, PredLinker)
lowerStatement _ lowerState0 _ linkPred (Assignment lhs rhs) =
  let assSid = lsSid lowerState0
      lowerState1 = linkPred (lowerState0 { lsSid = assSid + 1 }) [(None, assSid)]
      dPush' = dInsert (assSid, makeInputSet [T.pack "stm"])
               [(Assign lhs rhs, assSid)]
               (lsDPush lowerState1)

      linkAss ls succStates =
        let dPop' = dInsert (assSid, assSid) succStates (lsDPop ls)
        in ls { lsDPop = dPop' }

  in (lowerState1 { lsDPush = dPush' }, linkAss)

lowerStatement _ lowerState0 _ linkPred (Nondeterministic lval) =
  let assSid = lsSid lowerState0
      lowerState1 = linkPred (lowerState0 { lsSid = assSid + 1 }) [(None, assSid)]
      dPush' = dInsert (assSid, makeInputSet [T.pack "stm"])
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
      dPush'' = M.insert (callSid, makeInputSet $ [T.pack "call", fname] ++ skModules calleeSk)
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
        let dPushH = dInsert (hanSid, makeInputSet [T.pack "han"])
                     successorStates (lsDPush lowerState)
        in lowerState { lsDPush = dPushH }

      (ls2, linkPredTry) = lowerBlock sks ls1 thisFinfo linkHandler try
      -- add dummy exc to exit try block
      ls3 = linkPredTry ls2 [(None, dummySid0)]
      dShift' = M.insert (dummySid0, makeInputSet [T.pack "exc"])
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
type VarValuation = (Map Text IntValue, Map Text ArrayValue)
type VarState = (Word, VarValuation)

-- TODO: see if there's a better way of doing this
instance (Hashable k, Hashable v) => Hashable (Map k v) where
  hashWithSalt s m = hashWithSalt s $ M.toList m

initialValuation :: Set Variable -> VarValuation
initialValuation pvars = (scalars, arrays)
  where scalars = M.fromList
          $ map (\var -> (varName var, initVal var))
          $ filter (isScalar . varType)
          $ S.toList pvars
        arrays = M.fromList
          $ map (\var -> (varName var, V.replicate (arraySize . varType $ var) (initVal var)))
          $ filter (isArray . varType)
          $ S.toList pvars
        initVal = B.zeros . varWidth

programToOpa :: Bool -> Program -> Set (Prop Text)
             -> ( PropConv Text
                , [Prop APType]
                , [StructPrecRel APType]
                , [VarState]
                , VarState -> Bool
                , (E.BitEncoding -> VarState -> Input -> [VarState])
                , (E.BitEncoding -> VarState -> Input -> [VarState])
                , (VarState -> VarState -> [VarState])
                )
programToOpa isOmega (Program pvars sks) additionalProps =
  let (lowerState, ini, fin) = sksToExtendedOpa isOmega sks
      eInitials = [(sid, initVal) | sid <- ini]
        where initVal = initialValuation pvars
      eIsFinal (sid, _) = sid `S.member` finSet
        where finSet = S.fromList fin

      -- TODO: do everything with APType directly
      allProps = foldr S.insert additionalProps miniProcSls
      filterProps = M.mapKeysWith (\(States s1) (States s2) -> States $ s1 ++ s2)
                    (\(sid, props) -> (sid, S.filter (`S.member` allProps) props))
      lsFiltered = lowerState { lsDPush = filterProps $ lsDPush lowerState
                              , lsDShift = filterProps $ lsDShift lowerState
                              }
      pconv = makePropConv $ S.toList allProps
      allVarProps = S.fromList $ filter (`S.member` additionalProps) $ map (Prop . varName) $ S.toList pvars
      remapDeltaInput delta bitenc q b =
        applyDeltaInput allVarProps delta q (S.map (decodeProp pconv) $ E.decodeInput bitenc b)

  in ( pconv
     , map (encodeProp pconv) miniProcSls
     , encodeStructPrecRel pconv miniProcPrecRel
     , eInitials
     , if isOmega then const True else eIsFinal
     , remapDeltaInput $ lsDPush  lsFiltered
     , remapDeltaInput $ lsDShift lsFiltered
     , applyDeltaPop   $ lsDPop   lsFiltered
     )

applyDeltaInput :: Set (Prop Text)
                -> Map (Word, Set (Prop Text)) DeltaTarget
                -> VarState
                -> Set (Prop Text)
                -> [VarState]
applyDeltaInput allVarProps delta (sid, svval) lbl =
  let filterVars (Prop name) = toBool $ fst svval M.! name
      filterVars End = False

      svvalPropSet = S.filter filterVars allVarProps
      (varProps, lsProps) = S.partition (`S.member` allVarProps) lbl
  in if varProps == svvalPropSet
     then case M.lookup (sid, lsProps) delta of
            Nothing              -> []
            Just (States dsts)   -> concatMap (computeDst svval) dsts
            Just (EntryStates _) -> error "Expected States, got EntryStates."
     else []

applyDeltaPop :: Map (Word, Word) DeltaTarget
              -> VarState
              -> VarState
              -> [VarState]
applyDeltaPop delta (sid, svval) (stackSid, _) =
  case M.lookup (sid, stackSid) delta of
    Nothing              -> []
    Just (States dsts)   -> concatMap (computeDst svval) dsts
    Just (EntryStates _) -> error "Expected States, got EntryStates."

computeDst :: VarValuation -> (Label, Word) -> [VarState]
computeDst vval (None, dst) = [(dst, vval)]
computeDst vval@(ival, aval) (Assign (LScalar lhs) rhs, dst) =
  [(dst, (M.insert (varName lhs) (evalExpr vval rhs) ival, aval))]
computeDst vval@(ival, _) (Assign (LArray var idxExpr) rhs, dst) =
  [(dst, (ival, arrayAssign vval (evalExpr vval rhs) var idxExpr))]
computeDst vval (Guard g, dst)
  | toBool $ evalExpr vval g = [(dst, vval)]
  | otherwise = []
computeDst (ival, aval) (Nondet (LScalar var), dst) =
  map (\val -> (dst, (M.insert (varName var) val ival, aval))) $ enumerateIntType (varType var)
computeDst vval@(ival, _) (Nondet (LArray var idxExpr), dst) =
  map (\val -> (dst, (ival, arrayAssign vval val var idxExpr))) $ enumerateIntType (varType var)

arrayAssign :: VarValuation
            -> IntValue
            -> Variable
            -> Expr
            -> Map Text (Vector IntValue)
arrayAssign vval@(_, aval) val var idxExpr =
  M.adjust (\arr -> arr V.// [(idx, val)]) (varName var) aval
  where idx = fromEnum . B.nat . evalExpr vval $ idxExpr

evalExpr :: VarValuation -> Expr -> IntValue
evalExpr _ (Literal val) = val
evalExpr (ival, _) (Term var) = ival M.! varName var
evalExpr vval@(_, aval) (ArrayAccess var idxExpr) =
  (aval M.! varName var) V.! (fromEnum . B.nat . evalExpr vval $ idxExpr)
evalExpr vval (Not bexpr) = B.fromBool . not . toBool $ evalExpr vval bexpr
evalExpr vval (And lhs rhs) =
  B.fromBool $ (toBool $ evalExpr vval lhs) && (toBool $ evalExpr vval rhs)
evalExpr vval (Or lhs rhs) =
  B.fromBool $ (toBool $ evalExpr vval lhs) || (toBool $ evalExpr vval rhs)
evalExpr vval (Add lhs rhs) = evalExpr vval lhs + evalExpr vval rhs
evalExpr vval (Sub lhs rhs) = evalExpr vval lhs - evalExpr vval rhs
evalExpr vval (Mul lhs rhs) = evalExpr vval lhs * evalExpr vval rhs
evalExpr vval (UDiv lhs rhs) = evalExpr vval lhs `div` noDiv0 (evalExpr vval rhs)
evalExpr vval (SDiv lhs rhs) = evalExpr vval lhs `B.sdiv` noDiv0 (evalExpr vval rhs)
evalExpr vval (URem lhs rhs) = evalExpr vval lhs `mod` noDiv0 (evalExpr vval rhs)
evalExpr vval (SRem lhs rhs) = evalExpr vval lhs `B.smod` noDiv0 (evalExpr vval rhs)
evalExpr vval (Eq lhs rhs) = B.fromBool $ evalExpr vval lhs == evalExpr vval rhs
evalExpr vval (ULt lhs rhs) = B.fromBool $ evalExpr vval lhs < evalExpr vval rhs
evalExpr vval (ULeq lhs rhs) = B.fromBool $ evalExpr vval lhs <= evalExpr vval rhs
evalExpr vval (SLt lhs rhs) = B.fromBool $ evalExpr vval lhs `B.slt` evalExpr vval rhs
evalExpr vval (SLeq lhs rhs) = B.fromBool $ evalExpr vval lhs `B.sle` evalExpr vval rhs
evalExpr vval (UExt size op) = B.zeroExtend size $ evalExpr vval op
evalExpr vval (SExt size op) = B.signExtend size $ evalExpr vval op
evalExpr vval (Trunc size op) = evalExpr vval op B.@@ (size - 1, 0)

toBool :: IntValue -> Bool
toBool v = B.nat v /= 0

-- TODO: try removing this
noDiv0 :: IntValue -> IntValue
noDiv0 v | B.nat v /= 0 = v
         | otherwise = B.ones $ B.size v


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

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
                     , FunctionName
                     , Type(..)
                     , VarState
                     , isSigned
                     , typeWidth
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
import GHC.Generics (Generic)
import Data.Hashable

-- import qualified Debug.Trace as DBG

-- Intermediate representation for MiniProc programs
type FunctionName = Text
data Type = UInt Int | SInt Int deriving (Show, Eq, Ord, Generic)
data Variable = Variable { varType :: Type
                         , varName :: Text
                         } deriving (Show, Eq, Ord, Generic)
type IntValue = BitVector
data Expr = Literal IntValue
          | Term Variable
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
data Statement = Assignment Variable Expr
               | Nondeterministic Variable
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

isSigned :: Type -> Bool
isSigned (SInt _) = True
isSigned _ = False

typeWidth :: Type -> Int
typeWidth (UInt w) = w
typeWidth (SInt w) = w

commonType :: Type -> Type -> Type
commonType (UInt w0) (UInt w1) = UInt $ max w0 w1
commonType (UInt w0) (SInt w1) = SInt $ max w0 w1
commonType (SInt w0) (UInt w1) = SInt $ max w0 w1
commonType (SInt w0) (SInt w1) = SInt $ max w0 w1

varWidth :: Variable -> Int
varWidth = typeWidth . varType

enumerateIntType :: Type -> [IntValue]
enumerateIntType ty = B.bitVecs len [(0 :: Integer)..((2 :: Integer)^len-1)]
  where len = typeWidth ty


-- Generation of the Extended OPA

-- Data structures
data Label = None | Assign Variable Expr | Guard Expr | Nondet Variable deriving Show
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
                             , lsLoopEntries :: [(Label, Word)]
                             } deriving Show

sksToExtendedOpa :: Bool -> [FunctionSkeleton] -> (LowerState, [Word], [Word])
sksToExtendedOpa False sks = (buildExtendedOpa sks, [0], [1]) -- Finite case
sksToExtendedOpa True sks = -- Omega case
  let lowerState = buildExtendedOpa sks
      -- Add stuttering transitions
      dPush = M.insert (1, makeInputSet [T.pack "stm"]) (States [(None, 1)]) (lsDPush lowerState)
      dPop = M.insert (1, 1) (States [(None, 1)]) (lsDPop lowerState)

      fins = 1 : (concatMap (map snd . fiEntry) $ M.elems (lsFinfo lowerState))
               ++ map snd (lsLoopEntries lowerState)
  in ( lowerState { lsDPush = dPush, lsDPop = dPop }
     , [0]
     , S.toList . S.fromList $ fins)

buildExtendedOpa :: [FunctionSkeleton] -> LowerState
buildExtendedOpa sks =
  let lowerState = lowerFunction sksMap (LowerState M.empty M.empty M.empty M.empty 3 []) (head sks)
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

lowerStatement _ lowerState0 _ linkPred (Nondeterministic var) =
  let assSid = lsSid lowerState0
      lowerState1 = linkPred (lowerState0 { lsSid = assSid + 1 }) [(None, assSid)]
      dPush' = dInsert (assSid, makeInputSet [T.pack "stm"])
               [(Nondet var, assSid)]
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
        let enterEdges = case guard of
                           Just bexp -> map (\(lbl, s) -> (combGuards bexp lbl, s)) succStates
                           Nothing -> succStates
            lowerState1 = linkPred0 (linkBody lowerState0 enterEdges) enterEdges
        in lowerState1 { lsLoopEntries = lsLoopEntries lowerState1 ++ enterEdges }

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
type VarValuation = Map Variable IntValue
type VarState = (Word, VarValuation)
data ExpandData = ExpandData { edDPush :: Map (VarState, Set (Prop Text)) [VarState]
                             , edDShift :: Map (VarState, Set (Prop Text)) [VarState]
                             , edDPop :: Map (VarState, Word) [VarState]
                             , edVisited :: Set VarState
                             } deriving Show

-- TODO: see if there's a better way of doing this
instance (Hashable k, Hashable v) => Hashable (Map k v) where
  hashWithSalt s m = hashWithSalt s $ M.toList m

edInsert :: (Ord k) => k -> [v] -> Map k [v] -> Map k [v]
edInsert _ [] m = m
edInsert key vals m =
  case M.lookup key m of
    Nothing      -> M.insert key vals m
    Just oldVals -> M.insert key (oldVals ++ vals) m

initialValuation :: Set Variable -> VarValuation
initialValuation pvars = M.fromSet (\idf -> B.zeros $ varWidth idf) pvars

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
programToOpa omega (Program pvars sks) additionalProps =
  let (lowerState, ini, fin) = sksToExtendedOpa omega sks
      eInitials = [(sid, initVal) | sid <- ini]
        where initVal = initialValuation pvars
      ed0 = ExpandData M.empty M.empty M.empty S.empty
      ed1 = foldr (visitState lowerState) ed0 eInitials
      ed2 = addLabels additionalProps ed1
      eIsFinal (sid, _) = sid `S.member` finSet
        where finSet = S.fromList fin

      maybeList Nothing = []
      maybeList (Just l) = l

      -- TODO: do everything with APType directly
      pconv = makePropConv (miniProcSls ++ S.toList additionalProps)
      remapDeltaInput delta bitenc q b =
        maybeList $ M.lookup (q, S.map (decodeProp pconv) $ E.decodeInput bitenc b) delta

  in ( pconv
     , map (encodeProp pconv) miniProcSls
     , encodeStructPrecRel pconv miniProcPrecRel
     , eInitials
     , eIsFinal
     , remapDeltaInput $ edDPush ed2
     , remapDeltaInput $ edDShift ed2
     , \q (sid, _) -> maybeList $ M.lookup (q, sid) (edDPop ed2)
     )


addLabels :: Set (Prop Text) -> ExpandData -> ExpandData
addLabels additionalProps expandData =
  expandData { edDPush = addProps $ edDPush expandData
             , edDShift = addProps $ edDShift expandData
             }
  where filterVars :: (Variable, IntValue) -> Bool
        filterVars (var, val) = toBool val && Prop (varName var) `S.member` additionalProps

        stateToPropSet :: VarState -> Set (Prop Text)
        stateToPropSet (_, vval) =
          S.fromList $ map (Prop . varName . fst) $ filter filterVars $ M.toAscList vval
          -- TODO: maybe use varName as key so we don't have to call M.toAscList

        allowedProps :: Set (Prop Text)
        allowedProps = foldr S.insert additionalProps (End : miniProcSls)

        addProps :: Map (VarState, Set (Prop Text)) [VarState]
                 -> Map (VarState, Set (Prop Text)) [VarState]
        addProps delta = M.mapKeysWith (++)
          (\(s, lbl) -> (s, (lbl `S.intersection` allowedProps) `S.union` stateToPropSet s))
          delta

visitState :: LowerState -> VarState -> ExpandData -> ExpandData
visitState lowerState s@(sid, svval) expandData
  | s `S.member` edVisited expandData = expandData
  | otherwise =
    let ed0 = expandData { edVisited = S.insert s (edVisited expandData) }
        filterStates ((src, _), _) = src == sid
        pushSucc = filter filterStates (M.toList . lsDPush $ lowerState)
        ed1 = foldl (visitEdges svval updatePush lowerState) ed0 pushSucc
          where updatePush ed srcLbl dsts =
                  ed { edDPush = edInsert srcLbl dsts (edDPush ed) }
        shiftSucc = filter filterStates (M.toList . lsDShift $ lowerState)
        ed2 = foldl (visitEdges svval updateShift lowerState) ed1 shiftSucc
          where updateShift ed srcLbl dsts =
                  ed { edDShift = edInsert srcLbl dsts (edDShift ed) }
        popSucc = filter filterStates (M.toList . lsDPop $ lowerState)
        ed3 = foldl (visitEdges svval updatePop lowerState) ed2 popSucc
          where updatePop ed srcSid dsts =
                  ed { edDPop = edInsert srcSid dsts (edDPop ed) }
    in ed3

visitEdges :: Show a => VarValuation
           -> (ExpandData -> (VarState, a) -> [VarState] -> ExpandData)
           -> LowerState
           -> ExpandData
           -> ((Word, a), DeltaTarget)
           -> ExpandData
visitEdges vval updateDelta ls expandData ((src, lbl), (States dsts)) =
  foldl visitDst expandData dsts
  where visitDst ed0 ld =
          case caseDst ld of
            []      -> ed0
            newDsts -> let ed1 = updateDelta ed0 ((src, vval), lbl) newDsts
                       in foldr (visitState ls) ed1 newDsts

        caseDst :: (Label, Word) -> [VarState]
        caseDst (None, dst) = [(dst, vval)]
        caseDst (Assign lhs rhs, dst) = [(dst, M.insert lhs (evalExpr vval rhs) vval)]
        caseDst (Guard g, dst)
          | toBool $ evalExpr vval g = [(dst, vval)]
          | otherwise = []
        caseDst (Nondet var, dst) =
          map (\val -> (dst, M.insert var val vval)) $ enumerateIntType (varType var)
visitEdges _ _ _ _ (_, dt) = error $ "Expected States DeltaTarget, got " ++ show dt

evalExpr :: VarValuation -> Expr -> IntValue
evalExpr _ (Literal val) = val
evalExpr vval (Term var) = vval M.! var
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

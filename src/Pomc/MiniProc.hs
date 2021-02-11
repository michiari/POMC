{- |
   Module      : Pomc.MiniProc
   Copyright   : 2020 Michele Chiari
   License     : MIT
   Maintainer  : Michele Chiari
-}

module Pomc.MiniProc ( Program(..)
                     , FunctionSkeleton(..)
                     , Statement(..)
                     , Identifier
                     , FunctionName
                     , programToOpa
                     , skeletonsToOpa
                     ) where

import Pomc.Prop (Prop(..))
import Pomc.Prec (Prec(..), StructPrecRel)
import Pomc.ModelChecker (ExplicitOpa(..))

import Data.Text (Text)
import qualified Data.Text as T
import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S
import Data.Maybe (isNothing, fromJust)
import Data.BitVector (BitVector)
import qualified Data.BitVector as B


-- Intermediate representation for MiniProc programs
type FunctionName = Text
type Identifier = Text
data Statement = Assignment Identifier Bool
               | Call FunctionName
               | TryCatch [Statement] [Statement]
               | IfThenElse (Maybe Identifier) [Statement] [Statement]
               | Throw deriving Show
data FunctionSkeleton = FunctionSkeleton { skName :: FunctionName
                                         , skStmts :: [Statement]
                                         } deriving Show
data Program = Program { pVars :: Set Identifier
                       , pSks :: [FunctionSkeleton]
                       } deriving Show


-- Generation of the Extended OPA

-- Data structures
data Label = None | Assign Identifier Bool | Guard Identifier Bool deriving Show
data DeltaTarget = EntryStates Text | States [(Label, Word)] deriving Show

data FunctionInfo = FunctionInfo { fiEntry :: [(Label, Word)]
                                 , fiRetPad :: Word
                                 , fiThrow :: Word
                                 , fiExcPad :: Word
                                 }
data LowerState = LowerState { lsDPush :: Map (Word, Set (Prop Text)) DeltaTarget
                             , lsDShift :: Map (Word, Set (Prop Text)) DeltaTarget
                             , lsDPop :: Map (Word, Word) DeltaTarget
                             , lsFinfo :: Map Text FunctionInfo
                             , lsSid :: Word
                             }

sksToExtendedOpa :: [FunctionSkeleton] -> (LowerState, [Word], [Word])
sksToExtendedOpa sks =
  let lowerState = lowerFunction sksMap (LowerState M.empty M.empty M.empty M.empty 3) (head sks)
      sksMap = M.fromList $ map (\sk -> (skName sk, sk)) sks
      firstFname = skName $ head sks
      firstFinfo = fromJust $ M.lookup firstFname (lsFinfo lowerState)
      dPush' = M.insert (0, makeInputSet [T.pack "call", firstFname])
               (EntryStates firstFname) (lsDPush lowerState)
      dPop' = M.insert (fiRetPad firstFinfo, 0) (States [(None, 1)]) (lsDPop lowerState)
      dPop'' = M.insert (fiThrow firstFinfo, 0) (States [(None, 2)]) dPop'
      dPush'' = M.insert (2, makeInputSet [T.pack "exc"]) (States [(None, 1)]) dPush'
      dPop''' = M.insert (1, 2) (States [(None, 1)]) dPop''

      resolveTarget (EntryStates fname) =
        States . fiEntry . fromJust $ M.lookup fname (lsFinfo lowerState)
      resolveTarget x = x
      resolveAll deltaMap = M.map resolveTarget deltaMap
  in ( lowerState { lsDPush = resolveAll dPush''
                  , lsDShift = resolveAll $ lsDShift lowerState
                  , lsDPop = resolveAll dPop'''
                  }
     , [0]
     , [1]
     )

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

      dShift' = M.insert (sidRet, makeInputSet [T.pack "ret", skName fsk])
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
        let dPop' = dInsert (assSid, assSid)
                    (map (\(_, s) -> (Assign lhs rhs, s)) succStates)
                    (lsDPop ls)
        in ls { lsDPop = dPop' }

  in (lowerState1 { lsDPush = dPush' }, linkAss)


lowerStatement sks lowerState0 thisFinfo linkPred (Call fname) =
  let callSid = lsSid lowerState0
      calleeFinfo0 = M.lookup fname $ lsFinfo lowerState0
      lowerState1 = lowerState0 { lsSid = callSid + 1 }
      lowerState2 = if isNothing calleeFinfo0
                    then lowerFunction sks lowerState1 (fromJust $ M.lookup fname sks)
                    else lowerState1
      calleeFinfo1 = fromJust $ M.lookup fname (lsFinfo lowerState2)
      dPush'' = M.insert (callSid, makeInputSet [T.pack "call", fname])
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
          Just var -> linkPred0 lowerState (map (\(_, s) -> (Guard var True, s)) succStates)
          Nothing -> linkPred0 lowerState succStates
      linkPred0Else lowerState succStates =
        case guard of
          Just var -> linkPred0 lowerState (map (\(_, s) -> (Guard var False, s)) succStates)
          Nothing -> linkPred0 lowerState succStates

      (ls1, linkPred1) = lowerBlock sks ls0 thisFinfo linkPred0Then thenBlock
      (ls2, linkPred2) = lowerBlock sks ls1 thisFinfo linkPred0Else elseBlock
      linkPredITE lowerState succStates = linkPred2 (linkPred1 lowerState succStates) succStates
  in (ls2, linkPredITE)

lowerStatement _ lowerState thisFinfo linkPred Throw =
  (linkPred lowerState [(None, fiThrow thisFinfo)], (\ls _ -> ls))

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
type VarState = (Word, BitVector)
data ExpandData = ExpandData { edDPush :: Map (VarState, Set (Prop Text)) [VarState]
                             , edDShift :: Map (VarState, Set (Prop Text)) [VarState]
                             , edDPop :: Map (VarState, VarState) [VarState]
                             , edVisited :: Set VarState
                             }
type VarLookup = Identifier -> Int

edInsert :: (Ord k) => k -> [v] -> Map k [v] -> Map k [v]
edInsert _ [] m = m
edInsert key vals m =
  case M.lookup key m of
    Nothing      -> M.insert key vals m
    Just oldVals -> M.insert key (oldVals ++ vals) m

-- All possible valuations of nvars variables
allValuations :: Int -> [BitVector]
allValuations nvars = B.bitVecs nvars ([0..(2^nvars - 1)] :: [Integer])

programToOpa :: Program -> ExplicitOpa Word Text
programToOpa (Program pvars sks) =
  let (lowerState, ini, fin) = sksToExtendedOpa sks
      nvars = S.size pvars
      varLookup vname = fromJust $ M.lookup vname vmap
        where vmap = M.fromList $ zip (S.toList pvars) [0..nvars]
      eInitials = [(sid, bv) | sid <- ini, bv <- allValuations nvars]
      eFinals = [(sid, bv) | sid <- fin, bv <- allValuations nvars]
      ed0 = ExpandData M.empty M.empty M.empty S.empty
      ed1 = foldr (visitState lowerState varLookup) ed0 eInitials
      ed2 = varsToLabels pvars varLookup ed1

      remap :: VarState -> Word -> Map VarState Word -> (Word, Word, Map VarState Word)
      remap s count smap =
        case M.lookup s smap of
          Nothing  -> (count, count+1, M.insert s count smap)
          Just sid -> (sid, count, smap)
      remapList l oldCount oldSmap = foldr remapOne ([], oldCount, oldSmap) l
        where remapOne s (acc, count, smap) =
                let (sid, count', smap') = remap s count smap
                in (sid:acc, count', smap')
      remapPushShift delta oldCount oldSmap =
        foldr remapOne ([], oldCount, oldSmap) (M.toList delta)
        where remapOne ((p, lbl), qs) (acc, count, smap) =
                let (sidp, count', smap') = remap p count smap
                    (sidqs, count'', smap'') = remapList qs count' smap'
                in ((sidp, lbl, sidqs):acc, count'', smap'')
      remapPop delta oldCount oldSmap =
        foldr remapOne ([], oldCount, oldSmap) (M.toList delta)
        where remapOne ((p, st), qs) (acc, count, smap) =
                let (sidp, count', smap') = remap p count smap
                    (sidqs, count'', smap'') = remapList qs count' smap'
                    (sidst, count''', smap''') = remap st count'' smap''
                in ((sidp, sidst, sidqs):acc, count''', smap''')

      (rInitials, count0, smap0) = remapList eInitials 0 M.empty
      (rFinals, count1, smap1) = remapList eFinals count0 smap0
      (rDPush, count2, smap2) = remapPushShift (edDPush ed2) count1 smap1
      (rDShift, count3, smap3) = remapPushShift (edDShift ed2) count2 smap2
      (rDPop, _, _) = remapPop (edDPop ed2) count3 smap3
  in ExplicitOpa
     { sigma = (miniProcSls, map (Prop . skName) sks ++ map Prop (S.toList pvars))
     , precRel = miniProcPrecRel
     , initials = rInitials
     , finals = rFinals
     , deltaPush = rDPush
     , deltaShift = rDShift
     , deltaPop = rDPop
     }

varsToLabels :: Set Identifier -> VarLookup -> ExpandData -> ExpandData
varsToLabels pvars vidx expandData =
  expandData { edDPush = addProps $ edDPush expandData
             , edDShift = addProps $ edDShift expandData
             }
  where stateToPropSet :: VarState -> Set (Prop Text)
        stateToPropSet (_, bv) = S.map Prop $ S.filter (\v -> bv B.@. vidx v) pvars

        addProps :: Map (VarState, Set (Prop Text)) [VarState]
                 -> Map (VarState, Set (Prop Text)) [VarState]
        addProps delta = M.mapKeysWith (++) (\(s, lbl) -> (s, lbl `S.union` stateToPropSet s)) delta

visitState :: LowerState -> VarLookup -> VarState -> ExpandData -> ExpandData
visitState lowerState vidx s@(sid, svars) expandData
  | s `S.member` edVisited expandData = expandData
  | otherwise =
    let ed0 = expandData { edVisited = S.insert s (edVisited expandData) }
        filterStates ((src, _), _) = src == sid
        pushSucc = filter filterStates (M.toList . lsDPush $ lowerState)
        ed1 = foldl (visitEdges svars updatePush lowerState vidx) ed0 pushSucc
          where updatePush ed srcLbl dst =
                  ed { edDPush = edInsert srcLbl [dst] (edDPush ed) }
        shiftSucc = filter filterStates (M.toList . lsDShift $ lowerState)
        ed2 = foldl (visitEdges svars updateShift lowerState vidx) ed1 shiftSucc
          where updateShift ed srcLbl dst =
                  ed { edDShift = edInsert srcLbl [dst] (edDShift ed) }
        popSucc = filter filterStates (M.toList . lsDPop $ lowerState)
        ed3 = foldl (visitEdges svars updatePop lowerState vidx) ed2 popSucc
          where updatePop ed (src, stsid) dst =
                  let dPop' = foldl
                              (\dPop bv -> edInsert (src, (stsid, bv)) [dst] dPop)
                              (edDPop ed)
                              (allValuations (B.size svars))
                  in ed { edDPop = dPop' }
    in ed3

visitEdges :: BitVector
           -> (ExpandData -> (VarState, a) -> VarState -> ExpandData)
           -> LowerState
           -> VarLookup
           -> ExpandData
           -> ((Word, a), DeltaTarget)
           -> ExpandData
visitEdges vars updateDelta ls vidx expandData ((src, lbl), (States dsts)) =
  foldl visitDst expandData dsts
  where visitDst ed0 ld =
          let (ed1, maybeNewDst) = caseDst ed0 ld
          in case maybeNewDst of
               Just newDst -> visitState ls vidx newDst ed1
               Nothing     -> ed1

        caseDst :: ExpandData -> (Label, Word) -> (ExpandData, Maybe VarState)
        caseDst ed (None, dst) = (updateDelta ed ((src, vars), lbl) newDst, Just newDst)
          where newDst = (dst, vars)
        caseDst ed (Assign lhs rhs, dst) =
          let index = vidx lhs
              newVars = if rhs then B.setBit vars index else B.clearBit vars index
              newDst = (dst, newVars)
          in (updateDelta ed ((src, vars), lbl) newDst, Just newDst)
        caseDst ed (Guard g dir, dst)
          | vars B.@. vidx g == dir =
            let newDst = (dst, vars)
            in (updateDelta ed ((src, vars), lbl) newDst, Just newDst)
          | otherwise = (ed, Nothing)
visitEdges _ _ _ _ _ (_, dt) = error $ "Expected States DeltaTarget, got " ++ show dt

-- Generate a plain OPA directly (without variables)
skeletonsToOpa :: [FunctionSkeleton] -> ExplicitOpa Word Text
skeletonsToOpa sks = ExplicitOpa
  { sigma = (miniProcSls, map (Prop . skName) sks)
  , precRel = miniProcPrecRel
  , initials = ini
  , finals = fin
  , deltaPush = toListDelta $ lsDPush lowerState
  , deltaShift = toListDelta $ lsDShift lowerState
  , deltaPop = toListDelta $ lsDPop lowerState
  }
  where (lowerState, ini, fin) = sksToExtendedOpa sks
        toListDelta deltaMap = map normalize $ M.toList deltaMap
          where normalize ((a, b), States ls) =
                  (a, b, S.toList . S.fromList $ map snd ls)
                normalize (_, dt) = error $ "Expected States DeltaTarget, got " ++ show dt

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

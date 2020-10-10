{- |
   Module      : Pomc.OpaGen
   Copyright   : 2020 Michele Chiari
   License     : MIT
   Maintainer  : Michele Chiari
-}

module Pomc.OpaGen where

import Pomc.Prop (Prop(..))
import Pomc.ModelChecker (ExplicitOpa(..))
import Pomc.Example (stlPrecRelV2Text, stlPrecV2slsText)

import System.Random
import Data.Text (Text)
import qualified Data.Text as T
import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S
import Data.Maybe (isNothing, fromJust)

type FunctionName = Text
data Statement = Call FunctionName
               | TryCatch [Statement] [Statement]
               | IfThenElse [Statement] [Statement]
               | Throw deriving Show
data FunctionSkeleton = FunctionSkeleton { skName :: FunctionName
                                         , skStmts ::[Statement]
                                         } deriving Show


genIndices :: RandomGen g => g -> Int -> Int -> ([Int], g)
genIndices gen maxNum maxIndex =
  let (num, gen') = randomR (0, maxNum) gen
  in (iterate genIndex ([], gen')) !! num
  where genIndex (indices, oldGen) =
          let (idx, newGen) = randomR (0, maxIndex) oldGen
          in (idx : indices, newGen)

genFunctionSkeleton :: RandomGen g
                    => g
                    -> [FunctionName]
                    -> Int
                    -> FunctionName
                    -> (FunctionSkeleton, g)
genFunctionSkeleton gen fs maxCalls fname =
  let (statements, gen') = genBlock gen fs maxCalls [genTryCatch, genIfThenElse, genThrow]
  in (FunctionSkeleton fname statements, gen')

genBlock :: RandomGen g
         => g
         -> [FunctionName]
         -> Int
         -> [g -> [FunctionName] -> Int -> (Statement, g)]
         -> ([Statement], g)
genBlock gen fs maxCalls stmtGens =
  foldl createStatements ([], gen') stmtIndices
  where (stmtIndices, gen') = genIndices gen maxCalls (length fs + length stmtGens - 1)
        createStatements (stmts, oldGen) idx
          | idx < length fs = ((Call (fs !! idx)) : stmts, oldGen)
          | otherwise = let (tcStmt, newGen) = (stmtGens !! (idx - length fs)) oldGen fs maxCalls
                        in (tcStmt : stmts, newGen)

genTryCatch :: RandomGen g => g -> [FunctionName] -> Int -> (Statement, g)
genTryCatch gen fs maxCalls =
  let (try, gen') = genBlock gen fs maxCalls [genIfThenElse, genThrow]
      (catch, gen'') = genBlock gen' fs maxCalls [genIfThenElse]
  in (TryCatch try catch, gen'')

genIfThenElse :: RandomGen g => g -> [FunctionName] -> Int -> (Statement, g)
genIfThenElse gen fs maxCalls =
  let (thenBlock, gen') = genBlock gen fs maxCalls [genTryCatch, genIfThenElse, genThrow]
      (elseBlock, gen'') = genBlock gen' fs maxCalls [genTryCatch, genIfThenElse, genThrow]
  in (IfThenElse thenBlock elseBlock, gen'')

genThrow :: RandomGen g => g -> [FunctionName] -> Int -> (Statement, g)
genThrow gen _ _ = (Throw, gen)

genSkeletons :: RandomGen g => g -> Int -> Int -> ([FunctionSkeleton], g)
genSkeletons gen nf maxCalls = foldl foldSkeletons ([], gen) fs
  where fs = map (\n -> T.pack $ "p" ++ show n) [nf, nf-1 .. 0]
        foldSkeletons (sks, oldGen) fname =
          let (sk, newGen) = genFunctionSkeleton oldGen fs maxCalls fname
          in (sk : sks, newGen)


printFunctions :: Int -> Int -> IO ()
printFunctions nf maxCalls = do
  gen <- newStdGen
  (skeletons, _) <- return $ genSkeletons gen nf maxCalls
  putStrLn $ show skeletons
  putStrLn . show $ skeletonsToOpa skeletons


skeletonsToOpa :: [FunctionSkeleton] -> ExplicitOpa Word Text
skeletonsToOpa sks = ExplicitOpa
  { sigma = (stlPrecV2slsText, map (Prop . skName) sks)
  , precRel = stlPrecRelV2Text
  , initials = [0]
  , finals = [1]
  , deltaPush = toListDelta $ dPush'
  , deltaShift = toListDelta $ lsDShift lowerState
  , deltaPop = toListDelta $ dPop'
  }
  where lowerState = lowerFunction sksMap (LowerState M.empty M.empty M.empty M.empty 2) (head sks)
        sksMap = M.fromList $ map (\sk -> (skName sk, sk)) sks
        toListDelta deltaMap = map (\((a, b), dt) -> (a, b, resolveTarget dt)) $ M.toList deltaMap
        firstFname = skName $ head sks
        firstFinfo = fromJust $ M.lookup firstFname (lsFinfo lowerState)
        dPush' = M.insert (0, makeInputSet [T.pack "call", firstFname])
                 (EntryStates firstFname) (lsDPush lowerState)
        dPop' = M.insert (fiRetPad firstFinfo, 0) (States [1]) (lsDPop lowerState)

        resolveTarget (EntryStates fname) =
          fiEntry . fromJust $ M.lookup fname (lsFinfo lowerState)
        resolveTarget (States s) = s


data DeltaTarget = EntryStates Text | States [Word]

data FunctionInfo = FunctionInfo { fiName :: Text
                                 , fiEntry :: [Word]
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

lowerFunction :: Map Text FunctionSkeleton
              -> LowerState
              -> FunctionSkeleton
              -> LowerState
lowerFunction sks lowerState0 fsk =
  let sidRet = lsSid lowerState0
      thisFinfo = FunctionInfo (skName fsk) [] (sidRet + 1) (sidRet + 2) (sidRet + 3)
      finfo' = M.insert (skName fsk) thisFinfo (lsFinfo lowerState0)
      lowerState1 = lowerState0 { lsFinfo = finfo', lsSid = sidRet + 4 }
      (lowerState2, linkPred, entryStates) =
        if null (skStmts fsk)
        then (lowerState1, (\ls _ -> ls), [sidRet])
        else lowerBlock sks lowerState1 thisFinfo (\ls _ -> ls) (skStmts fsk)
      dShift' = M.insert (sidRet, makeInputSet [T.pack "ret", skName fsk])
                 (States [fiRetPad thisFinfo]) (lsDShift lowerState2)
      dShift'' = M.insert (fiThrow thisFinfo, makeInputSet [T.pack "exc"])
                 (States [fiExcPad thisFinfo]) dShift'
      dPush'' = M.insert (fiThrow thisFinfo, makeInputSet [T.pack "exc"])
                (States [1]) (lsDPush lowerState2)
      dPop'' = M.insert (1, fiThrow thisFinfo) (States [1]) (lsDPop lowerState2)
      finfo'' = M.insert (skName fsk) (thisFinfo { fiEntry = entryStates }) (lsFinfo lowerState2)
  in linkPred (lowerState2 { lsDPush = dPush'', lsDShift = dShift'',
                             lsDPop = dPop'', lsFinfo = finfo'' }) [sidRet]

lowerStatement :: Map Text FunctionSkeleton
               -> LowerState
               -> FunctionInfo
               -> (LowerState -> [Word] -> LowerState)
               -> Statement
               -> (LowerState, LowerState -> [Word] -> LowerState, [Word])
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
               (States [fiThrow thisFinfo]) (lsDPop lowerState2)

      linkCall lowerState successorStates =
          let dPop' = M.insert (fiRetPad calleeFinfo1, callSid)
                      (States successorStates) (lsDPop lowerState)
          in lowerState { lsDPop = dPop' }

  in ( linkPred (lowerState2 { lsDPush = dPush'', lsDPop = dPop'', lsSid = lsSid lowerState2 + 1}) [callSid]
     , linkCall
     , [callSid] )

lowerStatement sks ls0 thisFinfo linkPred0 (TryCatch try catch) =
  let hanSid = lsSid ls0
      ls1 = linkPred0 (ls0 { lsSid = hanSid + 1 }) [hanSid]

      linkHandler lowerState successorStates =
        let dPushH = M.insert (hanSid, makeInputSet [T.pack "han"])
                     (States successorStates) (lsDPush lowerState)
        in lowerState { lsDPush = dPushH }

      linkCatch lowerState successorStates =
        let dPopC = M.insert (fiExcPad thisFinfo, hanSid)
                    (States successorStates) (lsDPop lowerState)
        in lowerState { lsDPop = dPopC }

      (ls2, linkPred1, _) = lowerBlock sks ls1 thisFinfo linkHandler try
      (ls3, linkPred2, _) = lowerBlock sks ls2 thisFinfo linkCatch catch
      linkTryCatch ls succStates = linkPred2 (linkPred1 ls succStates) succStates

  in (ls3, linkTryCatch, [hanSid])

lowerStatement sks ls0 thisFinfo linkPred0 (IfThenElse thenBlock elseBlock) =
  let (ls1, linkPred1, entryThen) = lowerBlock sks ls0 thisFinfo (\ls _ -> ls) thenBlock
      (ls2, linkPred2, entryElse) = lowerBlock sks ls1 thisFinfo (\ls _ -> ls) elseBlock
      entryITE = entryThen ++ entryElse
      ls3 = linkPred0 ls2 entryITE
      linkPredITE lowerState succStates = linkPred2 (linkPred1 lowerState succStates) succStates
  in (ls3, linkPredITE, entryITE)

lowerStatement _ lowerState thisFinfo linkPred Throw =
  ( linkPred lowerState [fiThrow thisFinfo]
  , (\ls _ -> ls)
  , [fiThrow thisFinfo]
  )

lowerBlock :: Map Text FunctionSkeleton
           -> LowerState
           -> FunctionInfo
           -> (LowerState -> [Word] -> LowerState)
           -> [Statement]
           -> (LowerState, LowerState -> [Word] -> LowerState, [Word])
lowerBlock sks lowerState _ linkPred [] = (lowerState, linkPred, [])
lowerBlock sks lowerState thisFinfo linkPred block =
  foldBlock lowerStateH linkPredH (tail block)
  where (lowerStateH, linkPredH, entryStates) =
          lowerStatement sks lowerState thisFinfo linkPred (head block)

        foldBlock lowerState1 linkPred1 [] = (lowerState1, linkPred1, entryStates)
        foldBlock lowerState1 linkPred1 (Throw : stmts) =
          let (lowerState2, linkPred2, _) =
                lowerStatement sks lowerState1 thisFinfo linkPred1 Throw
          in (lowerState2, linkPred2, entryStates)
        foldBlock lowerState1 linkPred1 (stmt : stmts) =
          let (lowerState2, linkPred2, _) =
                lowerStatement sks lowerState1 thisFinfo linkPred1 stmt
          in foldBlock lowerState2 linkPred2 stmts


insertAll :: Ord k => [(k, v)] -> Map k v -> Map k v
insertAll kvPairs m = m `M.union` M.fromList kvPairs

makeInputSet :: (Ord a) => [a] -> Set (Prop a)
makeInputSet ilst = S.fromList $ map Prop ilst

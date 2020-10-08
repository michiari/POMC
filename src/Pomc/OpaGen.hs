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
data Statement = Call FunctionName | TryCatch [Statement] [Statement] deriving Show
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
  let (callIndices, gen') = genIndices gen maxCalls (length fs)
      (statements, gen'') = foldl createStatements ([], gen') callIndices
  in (FunctionSkeleton fname statements, gen'')

  where createStatements (stmts, oldGen) idx
          | idx < length fs = ((Call (fs !! idx)) : stmts, oldGen)
          | otherwise = let (tcStmt, newGen) = genTryCatch oldGen fs maxCalls
                        in (tcStmt : stmts, newGen)

genTryCatch :: RandomGen g => g -> [FunctionName] -> Int -> (Statement, g)
genTryCatch gen fs maxCalls =
  let (try, gen') = genBlock gen
      (catch, gen'') = genBlock gen'
  in (TryCatch try catch, gen'')

  where genBlock oldGen =
          let (callIndices, newGen) = genIndices oldGen maxCalls (length fs - 1)
          in (map (\idx -> Call (fs !! idx)) callIndices, newGen)

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
  where lowerState = lowerFunction sksMap (LowerState M.empty M.empty M.empty M.empty 2)
                     [firstFname] (head sks)
        sksMap = M.fromList $ map (\sk -> (skName sk, sk)) sks
        toListDelta deltaMap = map (\((a, b), c) -> (a, b, c)) $ M.toList deltaMap
        firstFname = skName $ head sks
        firstFinfo = fromJust $ M.lookup firstFname (lsFinfo lowerState)
        dPush' = M.insert (0, makeInputSet [T.pack "call", firstFname])
                 (fiEntry firstFinfo) (lsDPush lowerState)
        dPop' = M.insert (fiRetPad firstFinfo, 0) [1] (lsDPop lowerState)

data FunctionInfo = FunctionInfo { fiName :: Text
                                 , fiEntry :: [Word]
                                 , fiRetPad :: Word
                                 , fiThrow :: Word
                                 , fiExcPad :: Word
                                 }
data LowerState = LowerState { lsDPush :: Map (Word, Set (Prop Text)) [Word]
                             , lsDShift :: Map (Word, Set (Prop Text)) [Word]
                             , lsDPop :: Map (Word, Word) [Word]
                             , lsFinfo :: Map Text FunctionInfo
                             , lsSid :: Word
                             }

lowerFunction :: Map Text FunctionSkeleton
              -> LowerState
              -> [Text]
              -> FunctionSkeleton
              -> LowerState
lowerFunction sks lowerState0 stack fsk =
  let sid0 = lsSid lowerState0
      thisFinfo = FunctionInfo (skName fsk) [sid0] (sid0+1) (sid0+2) (sid0+3)
      finfo' = M.insert (skName fsk) thisFinfo (lsFinfo lowerState0)
      ((lowerState1, linkPred), sidRet) =
        if null (skStmts fsk)
        then ((lowerState0 { lsFinfo = finfo' }, (\ls _ -> ls)), sid0)
        else ( lowerBlock sks (lowerState0 { lsFinfo = finfo', lsSid = sid0 + 5 })
               stack sid0 (\ls _ -> ls) (skStmts fsk)
             , sid0 + 4 )
      dShift'' = M.insert (sidRet, makeInputSet [T.pack "ret", skName fsk])
                 [fiRetPad thisFinfo] (lsDShift lowerState1)
  in linkPred (lowerState1 { lsDShift = dShift'' }) [sidRet]

lowerStatement :: Map Text FunctionSkeleton
               -> LowerState
               -> [Text]
               -> Word
               -> (LowerState -> [Word] -> LowerState)
               -> Statement
               -> (LowerState, LowerState -> [Word] -> LowerState)
lowerStatement sks lowerState0 stack startSid linkPred (Call fname) =
  let calleeFinfo0 = M.lookup fname $ lsFinfo lowerState0
      lowerState1 = if isNothing calleeFinfo0
                    then lowerFunction sks lowerState0 (fname : stack) (fromJust $ M.lookup fname sks)
                    else lowerState0
      calleeFinfo1 = fromJust $ M.lookup fname (lsFinfo lowerState1)
      dPush'' = M.insert (startSid, makeInputSet [T.pack "call", fname])
                (fiEntry calleeFinfo1) (lsDPush lowerState1)

      linkCall lowerState successorStates =
          let dPop' = M.insert (fiRetPad calleeFinfo1, startSid)
                      successorStates (lsDPop lowerState)
          in lowerState { lsDPop = dPop' }

  in (linkPred (lowerState1 { lsDPush = dPush'', lsSid = lsSid lowerState1 + 1}) [startSid],
      linkCall)

lowerStatement sks ls0 stack startSid0 linkPred0 (TryCatch try catch) =
  let ls1 = linkPred0 ls0 [startSid0]
      startSid1 = lsSid ls1 + 1
      dPushH = M.insert (startSid0, makeInputSet [T.pack "han"]) [startSid1] (lsDPush ls0)
      (ls2, linkPred1) = lowerBlock sks (ls1 { lsDPush = dPushH, lsSid = startSid1 + 1 })
                         stack startSid1 (\ls _ -> ls) try
      (ls3, linkPred2) = lowerBlock sks ls2 stack (lsSid ls2) (\ls _ -> ls) catch
      linkTryCatch ls succStates = linkPred2 (linkPred1 ls succStates) succStates
  in (ls3, linkTryCatch)


lowerBlock :: Map Text FunctionSkeleton
           -> LowerState
           -> [Text]
           -> Word
           -> (LowerState -> [Word] -> LowerState)
           -> [Statement]
           -> (LowerState, LowerState -> [Word] -> LowerState)
lowerBlock sks lowerState stack startSid linkPred block =
  fst $ foldl foldBlock ((lowerState, linkPred), startSid) block
  where foldBlock ((lowerState1, linkPred1), startSid1) stmt =
          let (lowerState2, linkPred2) =
                lowerStatement sks lowerState1 stack startSid1 linkPred1 stmt
          in ((lowerState2 { lsSid = lsSid lowerState2 + 1 }, linkPred2), lsSid lowerState2)


insertAll :: Ord k => [(k, v)] -> Map k v -> Map k v
insertAll kvPairs m = m `M.union` M.fromList kvPairs

makeInputSet :: (Ord a) => [a] -> Set (Prop a)
makeInputSet ilst = S.fromList $ map Prop ilst

{- |
   Module      : Pomc.Prob.RightContexts
   Copyright   : 2026 Francesco Pontiggia
   License     : MIT
   Maintainer  : Francesco Pontiggia
-}
module Pomc.Prob.RightContexts ( RightContextGlobals
                               , computeRightContexts
                               ) where
import Data.IntSet(IntSet)
import qualified Data.IntSet as IntSet

import Data.Vector(Vector)
import qualified Data.Vector as V
import qualified Data.Vector.Mutable as MV

import qualified Data.Strict.IntMap as StrictIntMap
import Data.Strict.IntMap(IntMap)

import Pomc.IOStack(IOStack)
import qualified Pomc.IOStack as IOGS

import Control.Monad(when, forM_)
import Data.IORef (IORef, modifyIORef', readIORef, modifyIORef', newIORef)
import Data.Maybe (mapMaybe)

-- mutable global data structures of this module
data RightContextGlobals = RightContextGlobals
  { negIdSeq        :: IORef Int
  , sStack          :: IOStack Int
  , bStack          :: IOStack Int
  , iVector         :: MV.IOVector Int
  , succSCCsMapRef  :: IORef (IntMap IntSet) -- (node id, ids of successor SCCs)
  , accRCsMapRef :: IORef (IntMap IntSet) -- (id of the SCC, ids of right contexts where the SCC can terminate)
  }

newRightContextGlobals :: Int -> IO RightContextGlobals
newRightContextGlobals len = do
  newIdSeq <- newIORef (-1)
  newSStack <- IOGS.new
  newBStack <- IOGS.new
  newIVector <- MV.replicate len 0
  newSuccSCCsMapRef <- newIORef StrictIntMap.empty
  newAccRCsMapRef <- newIORef StrictIntMap.empty
  return RightContextGlobals { negIdSeq = newIdSeq
                             , sStack = newSStack
                             , bStack = newBStack
                             , iVector = newIVector
                             , succSCCsMapRef = newSuccSCCsMapRef
                             , accRCsMapRef = newAccRCsMapRef
                             }

computeRightContexts :: Vector [Int] -> Vector IntSet -> IO (Vector Int, IntMap IntSet)
computeRightContexts succVec rcsVec =
 let len = V.length succVec
 in do
    globals <- newRightContextGlobals len
    -- explore the graph
    forM_ [0..(len-1)]
     (\id_ -> do
        iVal <- MV.unsafeRead (iVector globals) id_
        when (iVal == 0) $ do
         addtoPath globals id_
         dfs globals succVec rcsVec id_
     )
    fIVector <- V.freeze (iVector globals)
    rcMap <- readIORef (accRCsMapRef globals)
    return (fIVector, rcMap)

dfs :: RightContextGlobals -> Vector [Int] -> Vector IntSet -> Int -> IO ()
dfs globals succVec rcsVec id_ =
    let cases nextId_ nextIVal
            | (nextIVal == 0) = do
                addtoPath globals nextId_
                dfs globals succVec rcsVec nextId_
                -- mark the SCC as successor of the current node
                updatedIval <- MV.unsafeRead (iVector globals) nextId_
                when (updatedIval < 0) $ modifyIORef' (succSCCsMapRef globals)
                    (StrictIntMap.insertWith IntSet.union id_ (IntSet.singleton updatedIval))

            | (nextIVal < 0)  = modifyIORef' (succSCCsMapRef globals)
                (StrictIntMap.insertWith IntSet.union id_ (IntSet.singleton nextIVal))
            | (nextIVal > 0)  = merge globals nextId_
            | otherwise = error "unreachable error"

        follow nextId_ = MV.unsafeRead (iVector globals) nextId_ >>= cases nextId_
    in do
        mapM_ follow (succVec V.! id_)
        createComponent globals rcsVec id_

createComponent :: RightContextGlobals -> Vector IntSet -> Int -> IO ()
createComponent globals rcsVec currentId_ = do
    topB <- IOGS.peek $ bStack globals
    iVal <- MV.unsafeRead (iVector globals)  currentId_
    let cases
            | iVal /= topB = return ()
            | otherwise = do
                -- updating data structures of Gabow algorithm
                sccId <- freshIONegId (negIdSeq globals)
                IOGS.pop_ (bStack globals)
                sSize <- IOGS.size $ sStack globals
                poppedSemiconfs <- IOGS.multPop (sStack globals) (sSize - iVal + 1) -- the last one is the current semiconfId_
                forM_ poppedSemiconfs $ \id_ -> MV.unsafeWrite (iVector globals) id_ sccId
                -- keeping track of right contexts for each SCC
                succSCCsMap <- readIORef (succSCCsMapRef globals)
                accRCsMap <- readIORef (accRCsMapRef globals)
                let rcs = IntSet.unions . map (rcsVec V.!) $ poppedSemiconfs -- right contexts of the current SCC
                    succSCCs = IntSet.toList . IntSet.unions . mapMaybe (`StrictIntMap.lookup` succSCCsMap) $ poppedSemiconfs -- successor SCCs of the current SCC
                    succSCCsRCs = IntSet.unions . mapMaybe (`StrictIntMap.lookup` accRCsMap) $ succSCCs -- right contexts of successor SCCs
                modifyIORef' (accRCsMapRef globals) (StrictIntMap.insert sccId (IntSet.union rcs succSCCsRCs)) -- adding right contexts to the current SCC
    cases
addtoPath :: RightContextGlobals -> Int -> IO ()
addtoPath globals id_ = do
  IOGS.push (sStack globals) id_
  sSize <- IOGS.size $ sStack globals
  MV.unsafeWrite (iVector globals) id_ sSize
  IOGS.push (bStack globals) sSize

merge ::  RightContextGlobals -> Int -> IO ()
merge globals id_ = do
  iVal <- MV.unsafeRead (iVector globals) id_
  -- contract the B stack, that represents the boundaries between SCCs on the current path
  IOGS.popWhile_ (bStack globals) (iVal <)

freshIONegId :: IORef Int -> IO Int
freshIONegId idSeq = do
  curr <- readIORef idSeq
  modifyIORef' idSeq (+ (-1))
  return curr
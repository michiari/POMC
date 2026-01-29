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

import Control.Monad(when, forM_)
import Control.Monad.IO.Class (MonadIO(liftIO))

import Pomc.IOStack(IOStack)
import qualified Pomc.IOStack as IOGS

import Data.IORef (IORef, modifyIORef', readIORef, modifyIORef', newIORef)


-- mutable global data structure of this module
data RightContextGlobals = RightContextGlobals
  { negIdSeq        :: IORef Int
  , sStack          :: IOStack Int
  , bStack          :: IOStack Int
  , iVector         :: MV.IOVector Int
  , succSCCsMap  :: IORef (IntMap IntSet) -- (NODE, ids of successor SCCs)
  }

newRightContextGlobals :: (MonadIO m) => Int -> m RightContextGlobals
newRightContextGlobals len = liftIO $ do
  newIdSeq <- newIORef (-1)
  newSStack <- IOGS.new
  newBStack <- IOGS.new
  newIVector <- MV.replicate len 0
  newSuccSCCsMap <- newIORef StrictIntMap.empty
  return RightContextGlobals { negIdSeq = newIdSeq
                             , sStack = newSStack
                             , bStack = newBStack
                             , iVector = newIVector
                             , succSCCsMap = newSuccSCCsMap
                             }

computeRightContexts :: (MonadIO m) => Vector [Int] -> Vector IntSet -> m (Vector Int, IntMap IntSet)
computeRightContexts succVec rcsVec =
 let len = V.length succVec
 in do
    globals <- newRightContextGlobals len
    -- explore the graph
    forM_ [0..(len-1)]  
     (\id_ -> do
        iVal <- liftIO $ MV.unsafeRead (iVector globals) id_
        when (iVal == 0) $ do 
         liftIO $ addtoPath globals id_
         dfs globals succVec id_
     ) 

    --aggregate results
    fIVector <- liftIO $ V.freeze (iVector globals)
    fsuccSCCsMap <- liftIO $ readIORef (succSCCsMap globals)
    let rcMap = StrictIntMap.fromListWith IntSet.union . V.toList . V.zip fIVector $ rcsVec
        -- it is fundamental to ensure correctness that SCCs are adjusted in descending order 
        -- indeed, each SCC depends only on SCCs with a higher id 
        -- recall that SCCs are assigned negative ids
        succSCCsList = StrictIntMap.toDescList $ StrictIntMap.mapKeysWith IntSet.union (fIVector V.!) fsuccSCCsMap
        -- adjust = add to a SCC all right contexts of descendant SCCs
        adjustMap m [] = m
        adjustMap m ((id_, succSCCs):l) =
            let succSCCRCs = IntSet.unions $ map (m StrictIntMap.!) (IntSet.toList succSCCs)
                adjusted = StrictIntMap.adjust (IntSet.union succSCCRCs) id_ m
            in adjustMap adjusted l
        rcReMap = adjustMap rcMap succSCCsList

    return (fIVector, rcReMap)

dfs :: (MonadIO m) => RightContextGlobals -> Vector [Int] -> Int -> m ()
dfs globals succVec id_ =
    let cases nextId_ nextIVal
            | (nextIVal == 0) = do
                liftIO $ addtoPath globals nextId_
                dfs globals succVec nextId_
                -- add the successor to our list
                updatedIval <- liftIO $ MV.unsafeRead (iVector globals) nextId_
                when (updatedIval < 0) $ liftIO $ modifyIORef' (succSCCsMap globals)
                    (StrictIntMap.insertWith IntSet.union id_ (IntSet.singleton updatedIval))  

            | (nextIVal < 0)  = liftIO $ modifyIORef' (succSCCsMap globals)
                (StrictIntMap.insertWith IntSet.union id_ (IntSet.singleton nextIVal))
            | (nextIVal > 0)  = liftIO $ merge globals nextId_
            | otherwise = error "unreachable error"

        follow nextId_ = do
            nextIVal <- liftIO $ MV.unsafeRead (iVector globals) nextId_
            cases nextId_ nextIVal
    in do
        mapM_ follow (succVec V.! id_)
        createComponent globals id_

createComponent :: (MonadIO m) => RightContextGlobals -> Int -> m ()
createComponent globals currentId_ = do
    topB <- liftIO . IOGS.peek $ bStack globals
    iVal <- liftIO $ MV.unsafeRead (iVector globals)  currentId_
    let createC = liftIO $ do
            -- update data structures of Gabow algorithm
            sccId <- freshIONegId (negIdSeq globals)
            IOGS.pop_ (bStack globals)
            sSize <- IOGS.size $ sStack globals
            poppedSemiconfs <- IOGS.multPop (sStack globals) (sSize - iVal + 1) -- the last one is the current semiconfId_
            forM_ poppedSemiconfs $ \id_ -> MV.unsafeWrite (iVector globals) id_ sccId
        cases
            | iVal /= topB = return ()
            | otherwise = createC -- cannot reach a pop 
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
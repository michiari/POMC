{-# LANGUAGE HexFloatLiterals #-}
{-# LANGUAGE TupleSections #-}
{- |
   Module      : Pomc.Prob.FixPoint
   Copyright   : 2023 Michele Chiari
   License     : MIT
   Maintainer  : Michele Chiari
-}

module Pomc.Prob.FixPoint ( VarKey
                          , FixpEq(..)
                          , EqMap
                          , AugEqMap
                          , LiveEq(..)
                          , LEqSys
                          , ProbVec
                          , Monomial2(..)
                          , Polynomial2
                          , PolyVector
                          , evalMonomial
                          , evalPolynomial
                          , evalPolySys
                          , jacobiTimesX
                          , pminusXjacobi
                          , addFixpEq
                          , addFixpEqs
                          , toLiveEqMapWith
                          , evalEqSys
                          , approxFixpFrom
                          , approxFixpWithHint
                          , approxFixpNewtonWithHint
                          , defaultEps
                          , defaultMaxIters
                          , toRationalProbVec
                          , preprocessApproxFixp
                          , preprocessZeroApproxFixp
                          , containsEquation
                          , retrieveEquation
                          , retrieveEquations
                          , retrieveRightContexts
                          , liveVariables
                          ) where

import Pomc.Prob.ProbUtils (Prob, EqMapNumbersType)
import Pomc.LogUtils (MonadLogger)

import Data.Maybe (fromJust)
import Data.Ratio (approxRational)
import Control.Monad.IO.Class (MonadIO(liftIO))
import Data.IORef (modifyIORef', readIORef, IORef)

import Pomc.IOMapMap(IOMapMap)
import qualified Pomc.IOMapMap as MM

import Data.Set (Set)
import qualified Data.Set as Set

import qualified Data.Strict.Map as M
import Data.Foldable (foldl', foldMap')
import Data.Either (isLeft)
import Data.Monoid (Sum(..))
import Data.Bifunctor(second)
import Data.Vector (Vector)
import qualified Data.Vector as V

import Data.IntSet (IntSet)
import Data.IntMap(IntMap)
import qualified Data.IntMap as IntMap

import qualified Numeric.LinearAlgebra as LA
import qualified Numeric.LinearAlgebra.Data as LAD

type VarKey = (Int, Int)
data FixpEq n = PushEq [(Prob, VarKey, VarKey)]
              | ShiftEq [(Prob, VarKey)]
              | PopEq n
              deriving (Eq, Show)

type EqMap n = IORef (IOMapMap (FixpEq n))
-- keep track of live equations for huge equation systems
type AugEqMap n = (EqMap n, IORef (Set VarKey))

-- EqMap containing only preprocessed live equations
-- (Left Int) is the variable's index in the current probVec, 
-- (Right n) is the supplied actual value for already solved variables
data LiveEq n = PushLEq [(n, Either Int n, Either Int n)]
              | ShiftLEq [(n, Either Int n)]
              deriving Show

type LEqSys n = Vector (LiveEq n)
type ProbVec n = Vector n
type SparseMatrix n = [((Int,Int), Polynomial2 n)]
type EvalSparseMatrix n = [((Int,Int), n)]

-- Int values are variables' indexes in the current src 
-- n are constant coefficients
data Monomial2 n = Lin n Int
                 | Const n
                 deriving Show
type Polynomial2 n = [Monomial2 n]
type PolyVector n = Vector (Polynomial2 n)

evalMonomial :: Num n => ProbVec n -> Monomial2 n -> n
evalMonomial v m = case m of
  Lin c k1 -> c * (v V.! k1)
  Const c -> c

evalPolynomial :: Num n => Polynomial2 n -> ProbVec n -> n
evalPolynomial p v = getSum $ foldMap' (Sum . evalMonomial v) p

evalPolySys :: (Ord n, Fractional n) => PolyVector n -> ProbVec n -> ProbVec n
evalPolySys polySys src = V.map (`evalPolynomial` src) polySys

evalSparseMatrix :: (Ord n, Fractional n) => SparseMatrix n -> ProbVec n -> EvalSparseMatrix n
evalSparseMatrix m src = map (second (`evalPolynomial` src)) m

-- compute (J|v + I) x, where J|v is the Jacobian of leqSys evaluated on v,
-- I is the identity matrix, and x is the vector of all variables
jacobiTimesX :: Num n => LEqSys n -> ProbVec n -> PolyVector n
jacobiTimesX leqSys v =
  let jtxMonomial dPdx = Lin coeff
        where coeff = evalMonomial v dPdx
      jtxPush (p, Left k1, Left k2)
        | k1 == k2 = [jtxMonomial (Lin ((2 * p)) k1) k1]
        | otherwise = [jtxMonomial (Lin p k2) k1, jtxMonomial (Lin p k1) k2]
      jtxPush (p, Left k1, Right val) = [jtxMonomial (Const (p * val)) k1]
      jtxPush (p, Right val, Left k1)  = [jtxMonomial (Const (p * val)) k1]
      jtxPush _ = error "unexpected"

      sparseJTimesX k (PushLEq terms) = (Lin 1 k :) . concatMap jtxPush
        $ filter (\(_, eitherK1, eitherK2) -> isLeft eitherK1 || isLeft eitherK2) terms
      sparseJTimesX k (ShiftLEq terms) = (Lin 1 k :) . map
        (\(p, Left k1) -> jtxMonomial (Const p) k1)
        $ filter (\(_, eitherP) -> isLeft eitherP) terms

  in V.imap sparseJTimesX leqSys

-- compute symbolically (i.e., not evaluated) J(P - x), the Jacobian J of leqSys P minus the vector of all variables x
pminusXjacobi :: Num n => LEqSys n -> SparseMatrix n
pminusXjacobi leqSys =
  let addMonomial dPdx k = M.insertWith (++) k [dPdx]

      jPush acc (p, Left k1, Left k2)
        | k1 == k2 =  addMonomial (Lin (2 * p) k1) k1 acc
        | otherwise = addMonomial (Lin p k2) k1 (addMonomial (Lin p k1) k2 acc)
      jPush acc (p, Left k1, Right val) = addMonomial (Const (p * val)) k1 acc
      jPush acc (p, Right val, Left k1) = addMonomial (Const (p * val)) k1 acc
      jPush acc _ = acc

      jShift acc (p, Left k1) = addMonomial (Const p) k1 acc
      jShift acc _ = acc

      sparseJacobi k (PushLEq terms) = M.toList . M.mapKeys (k,) . foldl' jPush (M.singleton k [Const (-1)]) $ terms
      sparseJacobi k (ShiftLEq terms) =  M.toList . M.mapKeys (k,) . foldl' jShift (M.singleton k [Const (-1)]) $ terms

  in concat . V.imap sparseJacobi $ leqSys

addFixpEq :: MonadIO m => AugEqMap n -> VarKey -> FixpEq n -> m ()
addFixpEq (eqMap, lEqs) varKey eq@(PopEq _) = liftIO $ do
  uncurry (MM.insert eqMap) varKey eq
  modifyIORef' lEqs (Set.delete varKey)
addFixpEq (eqMap, lEqs) varKey eq = liftIO $ do
  uncurry (MM.insert eqMap) varKey eq
  modifyIORef' lEqs (Set.insert varKey)

addFixpEqs :: (MonadIO m) => AugEqMap n -> Int -> IntMap (FixpEq n) -> m ()
addFixpEqs  (eqMap, lEqs) semiconfId_ eqs = liftIO $ do
  MM.insertMap eqMap semiconfId_ eqs
  let isPopEq (PopEq _) = True
      isPopEq _ = False
      (popEqs, liveEqs) = IntMap.partition isPopEq eqs
  modifyIORef' lEqs (Set.union . Set.fromList . map (semiconfId_, ) . IntMap.keys $ liveEqs)
  modifyIORef' lEqs (\s -> Set.difference s (Set.fromList . map (semiconfId_, ) . IntMap.keys $ popEqs))

constructEitherWith :: (MonadIO m, Fractional k) => AugEqMap n -> VarKey -> Set VarKey -> (n -> k) -> m (Either Int k)
constructEitherWith (eqMap, _) k lVars f
  | (Just idx) <- Set.lookupIndex k lVars = return (Left idx)
  | otherwise = liftIO $ Right . (\(PopEq n) -> f n) . fromJust <$> uncurry (MM.lookupValue eqMap) k

toLiveEqMapWith :: (MonadIO m, Fractional k) => AugEqMap n -> (n -> k) -> m (LEqSys k)
toLiveEqMapWith (eqMap, lEqs) f = liftIO $ do
  lVars <- readIORef lEqs
  let createLivePush (p, k1, k2) = do
        eitherK1 <- constructEitherWith (eqMap, lEqs) k1 lVars f
        eitherK2 <- constructEitherWith (eqMap, lEqs) k2 lVars f
        return (fromRational p, eitherK1, eitherK2)
      createLiveShift (p, k1) = do
        eitherK1 <- constructEitherWith (eqMap, lEqs) k1 lVars f
        return (fromRational p, eitherK1)
      createEq k = do
        eq <- fromJust <$> uncurry (MM.lookupValue eqMap) k
        case eq of
          PushEq terms -> PushLEq <$> mapM createLivePush terms
          ShiftEq terms -> ShiftLEq <$> mapM createLiveShift terms
          _ -> error "A supposed live variable is actually dead"
  V.mapM createEq (V.fromList $ Set.toList lVars)

evalEqSysNewton :: SparseMatrix Double -> LEqSys Double
  -> (Double -> Double -> Bool) -> ProbVec Double -> (Bool, ProbVec Double)
evalEqSysNewton jMatrix leqMap checkRes src =
  let computEq oldV (PushLEq terms) = oldV - getSum (foldMap'
        (\(p, k1, k2) -> Sum $ p * (either (src V.!) id k1) * (either (src V.!) id k2)) terms)
      computEq oldV (ShiftLEq terms)  = oldV - getSum (foldMap'
        (\(p, k1) -> Sum $ p * either (src V.!) id k1) terms)

      rhs = V.zipWith computEq src leqMap -- x - P(x) (right-hand-side)
      jacobiEval = evalSparseMatrix jMatrix src -- J(P(x) - x) (matrix of coefficients in sparse form)
      delta = V.fromList . LAD.toList
        . LA.cgSolve False (LAD.mkSparse jacobiEval) 
        . LAD.vector . V.toList 
        $ rhs -- delta = x(k+1) - src
        
      checkNaN = isNaN $ delta V.! 0 -- either all NaN or none

      dest = V.zipWith (+) src delta
      (checkDest, evalDest) = evalEqSys leqMap checkRes dest

      msg = "NaN result." ++ "\nSource: " ++ show src ++ "\nDelta: " ++ show delta 
        ++  "\nRHS: " ++ show rhs ++ "\nJacobiEval: " ++ show jacobiEval ++ "\nJMatrix:" ++ show jMatrix

  in if checkNaN
      then error msg
      else (checkDest, evalDest)

checkIterNewton :: Double -> Double -> Double -> Bool 
checkIterNewton newtonEps newV oldV =
  -- delta <= eps -- absolute error
  (newV - oldV) / newV <= newtonEps -- relative error 

approxFixpFromNewton :: SparseMatrix Double -> LEqSys Double -> Double -> Double -> Int -> Int -> ProbVec Double -> ProbVec Double
approxFixpFromNewton _ leqMap _ viEps 0 maxItersVI probVec = approxFixpFrom leqMap viEps maxItersVI probVec
approxFixpFromNewton jMatrix leqMap newtonEps viEps maxItersNewton maxItersVI probVec =
  let (lessThanEps, newProbVec) = evalEqSysNewton jMatrix leqMap (checkIterNewton newtonEps) probVec
    in if lessThanEps
        then approxFixpFrom leqMap viEps maxItersVI newProbVec
        else approxFixpFromNewton jMatrix leqMap newtonEps viEps (maxItersNewton - 1) maxItersVI newProbVec

approxFixpNewtonWithHint :: (MonadIO m, MonadLogger m)
           => AugEqMap k -> (k -> Double) -> Double -> Double -> Int -> Int -> ProbVec Double -> m (ProbVec Double)
approxFixpNewtonWithHint augEqMap f eps viEps maxIters maxItersVI hint = do
  leqMap <- toLiveEqMapWith augEqMap f
  let (checkHint, evalHint) = evalEqSys leqMap (checkIterNewton viEps) hint
      jMatrix = pminusXjacobi leqMap
      approxVec = approxFixpFromNewton jMatrix leqMap eps viEps maxIters maxItersVI evalHint
  if checkHint -- the Newton method cannot deal with hints already at the fixpoint
    then return evalHint
    else return approxVec

-- Gauss-Seidel method --
evalEqSys :: (Show n, Ord n, Fractional n)
          => LEqSys n -> (n -> n -> Bool) -> ProbVec n -> (Bool, ProbVec n)
evalEqSys leqMap checkRes src =
  let -- Gauss-Seidel update (read from dest values for already evaluated eqs)
      -- for plain value iteration, always read from source
      getV i j = if j < i then dest V.! j else src V.! j
      computEq idx (PushLEq terms) = getSum $ foldMap'
        (\(p, k1, k2) -> Sum $ p * (either (getV idx) id k1) * (either (getV idx) id k2)) terms
      computEq idx (ShiftLEq terms) = getSum $ foldMap'
        (\(p, k1) -> Sum $ p * either (getV idx) id k1) terms
      dest = V.imap computEq leqMap
      checkDest = V.and (V.zipWith checkRes dest src)
  in (checkDest, dest)

approxFixpFrom :: (Ord n, Fractional n, Show n)
               => LEqSys n -> n -> Int -> ProbVec n -> ProbVec n
approxFixpFrom _ _ 0 probVec = probVec
approxFixpFrom leqMap eps maxIters probVec =
  -- should be newV >= oldV
  let checkIter newV oldV =
        -- newV - oldV <= eps -- absolute error
        newV == 0 || (newV - oldV) / newV <= eps -- relative error
      (lessThanEps, newProbVec) = evalEqSys leqMap checkIter probVec
  in if lessThanEps
      then newProbVec
      else  approxFixpFrom leqMap eps (maxIters - 1) newProbVec

approxFixpWithHint :: (MonadIO m, MonadLogger m, Ord n, Fractional n, Show n)
           => AugEqMap k -> (k -> n) -> n -> Int -> ProbVec n -> m (ProbVec n)
approxFixpWithHint augEqMap f eps maxIters hint = do
  leqMap <- toLiveEqMapWith augEqMap f
  return $ approxFixpFrom leqMap eps maxIters hint

-- determine variables for which zero is a fixpoint by iterating a few times the system
-- Note that we are not allowed to use the Newton method here, as it is not guaranteed to converge for non clean systems 
-- (cit. Computing the Least Fixed Point of Positive Polynomial Systems)
preprocessZeroApproxFixp :: (MonadIO m, MonadLogger m, Ord n, Fractional n, Show n, Show k)
                      => AugEqMap k -> (k -> n) -> n -> Int -> m (ProbVec n)
preprocessZeroApproxFixp augEqMap@(_, lVarsRef) f eps maxIters = do
  lVars <- liftIO $ readIORef lVarsRef
  if Set.null lVars
    then return V.empty
    else do
      leqMap <- toLiveEqMapWith augEqMap f
      return $ approxFixpFrom leqMap eps maxIters (V.replicate (Set.size lVars) 0)

-- preprocess live equations by propagating found values, until no value can be propagated anymore
preprocessApproxFixp :: (MonadIO m, MonadLogger m, Ord n, Fractional n, Show n, Show k)
                      => AugEqMap k -> (k -> n) -> m [(VarKey, n)]
preprocessApproxFixp augEqMap@(_, lVarsRef) f = do
  lVars <- liftIO $ readIORef lVarsRef
  if Set.null lVars
    then return []
    else do
      leqMap <- toLiveEqMapWith augEqMap f
      let solveShift _ Nothing _ = Nothing
          solveShift _ (Just acc) (p, Right v) = Just $ acc + p * v
          solveShift killedVars (Just acc) (p, Left idx)
            | (Just v) <- M.lookup k killedVars = Just $ acc + p * v
            | otherwise = Nothing
              where k = Set.elemAt idx lVars

          solvePush _ Nothing _ = Nothing
          solvePush _ (Just acc) (p, Right v1, Right v2) = Just $ acc + p * v1 * v2
          solvePush killedVars (Just acc) (p, Right v1, Left idx)
            | (Just v) <- M.lookup k killedVars = Just $ acc + p * v1 * v
            | otherwise = Nothing
              where k = Set.elemAt idx lVars
          solvePush killedVars (Just acc) (p, Left k, Right v1) = solvePush killedVars (Just acc) (p, Right v1, Left k)
          solvePush killedVars (Just acc) (p, Left idx1, Left idx2)
            | (Just v1) <- M.lookup k1 killedVars, (Just v2) <- M.lookup k2 killedVars = Just $ acc + p * v1 * v2
            | otherwise = Nothing
              where k1 = Set.elemAt idx1 lVars
                    k2 = Set.elemAt idx2 lVars

          solveEq killedVars eq = case eq of
            PushLEq terms ->  foldl' (solvePush killedVars)  (Just 0) terms
            ShiftLEq terms -> foldl' (solveShift killedVars) (Just 0) terms

          go (False, updatedVars, liveVars)  = (M.toList updatedVars, map fst liveVars)
          go (True, updatedVars, liveVars) = go $ foldl' (\(recurse, upVars, lVars) (varKey, eq) ->
            case solveEq updatedVars eq of
              Nothing -> (recurse, upVars, (varKey, eq):lVars)
              Just v  -> (True, M.insert varKey v upVars, lVars)
            ) (False, updatedVars, []) liveVars

          vars = zip (Set.toList lVars) (V.toList leqMap)
          (upVars, _) = go (True, M.empty, vars)
      return upVars

defaultEps :: EqMapNumbersType
defaultEps = 0x1p-26 -- ~ 1e-8

defaultMaxIters :: Int
defaultMaxIters = 1000000

toRationalProbVec :: (RealFrac n) => n -> ProbVec n -> ProbVec Prob
toRationalProbVec eps = V.map (\p -> approxRational (p - eps) eps)
-- p - eps is to prevent approxRational from producing a result > p

containsEquation :: (MonadIO m) => AugEqMap n -> VarKey -> m Bool
containsEquation (eqMap, _) varKey = liftIO $ uncurry (MM.member eqMap) varKey

retrieveEquation :: (MonadIO m) => AugEqMap n -> VarKey -> m (Maybe (FixpEq n))
retrieveEquation (eqMap, _) varKey = liftIO $ uncurry (MM.lookupValue eqMap) varKey

retrieveRightContexts :: (MonadIO m) => AugEqMap n -> Int -> m IntSet
retrieveRightContexts (eqMap, _) semiconfId_ = liftIO $ MM.lookupKeys eqMap semiconfId_

retrieveEquations :: (MonadIO m) => AugEqMap n -> Int -> m [(Int, FixpEq n)]
retrieveEquations (eqMap, _) semiconfId_ = liftIO $ MM.lookup eqMap semiconfId_

liveVariables :: (MonadIO m) => AugEqMap n ->  m (Vector VarKey)
liveVariables (_,lVarsRef) = V.fromList . Set.toList <$> liftIO (readIORef lVarsRef)
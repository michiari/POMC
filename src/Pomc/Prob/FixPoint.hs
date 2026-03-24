{-# LANGUAGE TupleSections #-}
{-# LANGUAGE InstanceSigs #-}
{- |
   Module      : Pomc.Prob.FixPoint
   Copyright   : 2023-2026 Michele Chiari, Francesco Pontiggia
   License     : MIT
   Maintainer  : Francesco Pontiggia
-}

module Pomc.Prob.FixPoint ( VarKey
                          , FixpEq(..)
                          , EqMap
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
                          , addPopEq
                          , addFixpEqs
                          , toLiveEqMapWith
                          , evalEqSys
                          , approxFixpFrom
                          , approxFixpFromAbove
                          , approxFixpNewtonWithHint
                          , toRationalProbVec
                          , retrieveEquation
                          , retrieveEquations
                          , retrieveEquationsMap
                          , retrieveRightContexts
                          ) where

import Pomc.Prob.ProbUtils (Prob)

import Pomc.IOMapMap(IOMapMap)
import qualified Pomc.IOMapMap as MM
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Strict.Map as M
import Data.Vector (Vector)
import qualified Data.Vector as V
import Data.IntSet (IntSet)
import Data.IntMap(IntMap)

import qualified Numeric.LinearAlgebra as LA
import qualified Numeric.LinearAlgebra.Data as LAD
import Data.Foldable (foldl', foldMap')
import Data.Maybe (fromJust)
import Data.Either (isLeft)
import Data.Monoid (Sum(..))
import Data.Bifunctor(second)
import Data.Ratio (approxRational)
import Control.Monad.IO.Class (MonadIO(liftIO))
import Data.IORef (IORef)

type VarKey = (Int, Int)
data FixpEq n = PushEq [(Prob, VarKey, VarKey)]
              | ShiftEq [(Prob, VarKey)]
              | PopEq n
              deriving (Eq, Show)

type EqMap n = IORef (IOMapMap (FixpEq n))

-- EqMap containing only preprocessed live equations
-- (Left Int) is the variable's index in the current probVec, 
-- (Right n) is the supplied actual value for already solved variables
data LiveEq n = PushLEq [(n, Either Int n, Either Int n)]
              | ShiftLEq [(n, Either Int n)]
              deriving Show

instance Functor LiveEq where
  fmap :: (a -> b) -> LiveEq a -> LiveEq b
  fmap f (PushLEq l) = PushLEq (map fPush l)
    where fPush (p, eith1, eith2) = (f p, fmap f eith1, fmap f eith2)
  fmap f (ShiftLEq l) = ShiftLEq (map fShift l)
    where fShift (p, eith1) = (f p, fmap f eith1)
    
type LEqSys n = Vector (LiveEq n)
type ProbVec n = Vector n
type SparseMatrix n = [(VarKey, Polynomial2 n)]
type EvalSparseMatrix n = [(VarKey, n)]

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
        | k1 == k2 = [jtxMonomial (Lin (2 * p) k1) k1]
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

      jacobi k f = M.toList . M.mapKeys (k,) . foldl' f (M.singleton k [Const (-1)])
      sparseJacobi k (PushLEq terms) = jacobi k jPush terms
      sparseJacobi k (ShiftLEq terms) = jacobi k jShift terms

  in concat . V.imap sparseJacobi $ leqSys

addPopEq :: MonadIO m => EqMap n -> VarKey -> n -> m ()
addPopEq eqMap varKey val = liftIO $ uncurry (MM.insert eqMap) varKey (PopEq val)

addFixpEqs :: (MonadIO m) => EqMap n -> Int -> IntMap (FixpEq n) -> m ()
addFixpEqs  eqMap semiconfId_ eqs = liftIO $ MM.insertMap eqMap semiconfId_ eqs

constructEitherWith :: (MonadIO m, Fractional k, Show n)
  => EqMap n -> VarKey -> Set VarKey -> (n -> k) -> m (Either Int k)
constructEitherWith eqMap k lVars f
  | (Just idx) <- Set.lookupIndex k lVars = return (Left idx)
  | otherwise = liftIO $ do
    maybeVal <- uncurry (MM.lookupValue eqMap) k
    return $ Right $ (\(PopEq n) -> f n) (fromJust maybeVal)

toLiveEqMapWith :: (MonadIO m, Fractional k, Show n, Eq k)
  => EqMap n -> Set VarKey -> (n -> k) -> m (LEqSys k)
toLiveEqMapWith eqMap lVars f = liftIO $ do
  let createLivePush (p, k1, k2) = do
        eitherK1 <- constructEitherWith eqMap k1 lVars f
        eitherK2 <- constructEitherWith eqMap k2 lVars f
        return (fromRational p, eitherK1, eitherK2)
      createLiveShift (p, k1) = do
        eitherK1 <- constructEitherWith eqMap k1 lVars f
        return (fromRational p, eitherK1)
      createEq k = do
        eq <- fromJust <$> uncurry (MM.lookupValue eqMap) k
        case eq of
          PushEq terms -> PushLEq <$> mapM createLivePush terms
          ShiftEq terms -> ShiftLEq <$> mapM createLiveShift terms
          _ -> error "A supposed live variable is actually dead"
  V.mapM createEq (V.fromList $ Set.elems lVars)

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
      (checkDest, evalDest) = evalEqSysAny leqMap checkRes dest

      msg = "NaN result." ++ "\nSource: " ++ show src ++ "\nDelta: " ++ show delta
        ++  "\nRHS: " ++ show rhs ++ "\nJacobiEval: "
        ++ show jacobiEval ++ "\nJMatrix:" ++ show jMatrix

  in if checkNaN
      then error msg
      else (checkDest, evalDest)

checkIterNewton :: Double -> Double -> Double -> Bool
checkIterNewton newtonEps newV oldV =
  -- delta <= eps -- absolute error
  (newV - oldV) / newV <= newtonEps -- relative error 

approxFixpFromNewton :: SparseMatrix Double -> LEqSys Double -> Double -> Double
  -> Int -> Int -> ProbVec Double -> ProbVec Double
approxFixpFromNewton _ leqMap _ viEps 0 maxItersVI probVec = approxFixpFrom leqMap viEps maxItersVI probVec
approxFixpFromNewton jMatrix leqMap newtonEps viEps maxItersNewton maxItersVI probVec =
  let (lessThanEps, newProbVec) = evalEqSysNewton jMatrix leqMap (checkIterNewton newtonEps) probVec
  in if lessThanEps
      then approxFixpFrom leqMap viEps maxItersVI newProbVec
      else approxFixpFromNewton jMatrix leqMap newtonEps viEps (maxItersNewton - 1) maxItersVI newProbVec

approxFixpNewtonWithHint :: LEqSys Double -> Double -> Double -> Int -> Int -> ProbVec Double -> ProbVec Double
approxFixpNewtonWithHint lEqMap eps viEps maxIters maxItersVI hint = do
  let (checkHint, evalHint) = evalEqSys lEqMap (checkIterNewton viEps) hint
      jMatrix = pminusXjacobi lEqMap
      approxVec = approxFixpFromNewton jMatrix lEqMap eps viEps maxIters maxItersVI evalHint
  if checkHint -- Newton's method cannot deal with hints already at the fixpoint
    then evalHint
    else approxVec

-- Gauss-Seidel method --
evalEqSysAny :: (Show n, Ord n, Fractional n)
  => LEqSys n -> (n -> n -> Bool) -> ProbVec n -> (Bool, ProbVec n)
evalEqSysAny leqMap checkRes src =
  let -- Gauss-Seidel update (read from dest values for already evaluated eqs)
      -- for plain value iteration, always read from source
      getV i j = if j < i then dest V.! j else src V.! j
      computEq idx (PushLEq terms) = getSum $ foldMap'
        (\(p, k1, k2) -> Sum $ p * (either (getV idx) id k1) * (either (getV idx) id k2)) terms
      computEq idx (ShiftLEq terms) = getSum $ foldMap'
        (\(p, k1) -> Sum $ p * either (getV idx) id k1) terms
      dest = V.imap computEq leqMap
      checkDest = V.or (V.zipWith checkRes dest src) -- OR instead of AND
  in (checkDest, dest)

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
approxFixpFrom _ _ 0 _ = error "Exhausted value iteration."
approxFixpFrom leqMap eps maxIters probVec =
  -- should be newV >= oldV
  let checkIter newV oldV =
        -- newV - oldV <= eps -- absolute error
        newV == 0 || (newV - oldV) / newV <= eps -- relative error
      (lessThanEps, newProbVec) = evalEqSys leqMap checkIter probVec
  in if lessThanEps
      then newProbVec
      else approxFixpFrom leqMap eps (maxIters - 1) newProbVec

-- same as approxFixpFrom, but used to approximate the fixpoint from above it, hence with decreasing approximations
approxFixpFromAbove :: (Ord n, Fractional n, Show n)
  => LEqSys n -> n -> Int -> ProbVec n -> ProbVec n
approxFixpFromAbove _ _ 0 probVec = probVec
approxFixpFromAbove leqMap eps maxIters probVec =
  -- should be oldV >= newV
  let checkIter newV oldV =
        -- oldV - newV <= eps -- absolute error
        newV == 0 || (oldV - newV) / newV <= eps -- relative error
      (lessThanEps, newProbVec) = evalEqSys leqMap checkIter probVec
  in if lessThanEps
      then newProbVec
      else approxFixpFromAbove leqMap eps (maxIters - 1) newProbVec

toRationalProbVec :: (RealFrac n) => n -> ProbVec n -> ProbVec Prob
toRationalProbVec eps = V.map (\p -> approxRational (p - eps) eps)
-- p - eps is to prevent approxRational from producing a result > p

retrieveEquation :: (MonadIO m) => EqMap n -> VarKey -> m (Maybe (FixpEq n))
retrieveEquation eqMap varKey = liftIO $ uncurry (MM.lookupValue eqMap) varKey

retrieveRightContexts :: (MonadIO m) => EqMap n -> Int -> m IntSet
retrieveRightContexts eqMap semiconfId_ = liftIO $ MM.lookupKeys eqMap semiconfId_

retrieveEquations :: (MonadIO m) => EqMap n -> Int -> m [(Int, FixpEq n)]
retrieveEquations eqMap semiconfId_ = liftIO $ MM.lookup eqMap semiconfId_

retrieveEquationsMap :: (MonadIO m) => EqMap n -> Int -> m (IntMap (FixpEq n))
retrieveEquationsMap eqMap semiconfId_ = liftIO $ MM.lookupMap eqMap semiconfId_
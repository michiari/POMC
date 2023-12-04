{-# LANGUAGE DeriveGeneric #-}

{- |
   Module      : Pomc.MiniProcUtils
   Copyright   : 2020-2023 Michele Chiari
   License     : MIT
   Maintainer  : Michele Chiari
-}

module Pomc.MiniProcUtils ( VarValuation(..)
                          , VarState
                          , initialValuation
                          , scalarAssign
                          , arrayAssign
                          , wholeArrayAssign
                          , evalExpr
                          , toBool
                          ) where

import Pomc.MiniIR

import Data.Set (Set)
import qualified Data.Set as S
import qualified Data.BitVector as B
import Data.Vector (Vector)
import qualified Data.Vector as V
import GHC.Generics (Generic)
import Data.Hashable

-- Data structures
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
          map (\var -> (getIdx True $ varOffset var, initialScalar var)) (S.toList svars)
        arrays = V.replicate (S.size avars) V.empty V.//
          map (\var -> (getIdx False $ varOffset var, initialArray var)) (S.toList avars)

        initialScalar = B.zeros . varWidth
        initialArray var = V.replicate (arraySize . varType $ var) (initialScalar var)

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
  where vid = varOffset var

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
  where vid = varOffset var
        idx = fromEnum . B.nat . evalExpr gvii vval $ idxExpr
        doAssign aval varIdx =
          aval V.// [(varIdx, (aval V.! varIdx) V.// [(idx, val)])]

wholeArrayAssign :: VarIdInfo
                 -> VarValuation
                 -> Variable
                 -> VarValuation
                 -> Variable
                 -> VarValuation
wholeArrayAssign gvii dstVval dstVar srcVval srcVar
  | isGlobal gvii False dstVid = dstVval {
      vGlobalArrays = vGlobalArrays dstVval V.// [(dstVid, srcVal)] }
  | otherwise = dstVval {
      vLocalArrays = vLocalArrays dstVval V.// [(getLocalIdx gvii False dstVid, srcVal)] }
  where dstVid = varOffset dstVar
        srcVid = varOffset srcVar
        srcVal | isGlobal gvii False srcVid = vGlobalArrays srcVval V.! srcVid
               | otherwise = vLocalArrays srcVval V.! getLocalIdx gvii False srcVid

evalExpr :: VarIdInfo -> VarValuation -> Expr -> IntValue
evalExpr _ _ (Literal val) = val
evalExpr gvii vval (Term var)
  | isGlobal gvii True vid = vGlobalScalars vval V.! vid
  | otherwise = vLocalScalars vval V.! getLocalIdx gvii True vid
  where vid = varOffset var
evalExpr gvii vval (ArrayAccess var idxExpr) =
  arr V.! (fromEnum . B.nat . evalExpr gvii vval $ idxExpr)
  where vid = varOffset var
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

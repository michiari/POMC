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
                          , miniProcAlphabet
                          , miniProcSls
                          ) where

import Pomc.MiniIR
import Pomc.Prop (Prop(..))
import Pomc.Prec (Prec(..), StructPrecRel, Alphabet)

import qualified Data.Text as T
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
          map (\var -> (getIdx True $ varId var, initialScalar var)) (S.toList svars)
        arrays = V.replicate (S.size avars) V.empty V.//
          map (\var -> (getIdx False $ varId var, initialArray var)) (S.toList avars)

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
  where vid = varId var

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
  where vid = varId var
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
  where dstVid = varId dstVar
        srcVid = varId srcVar
        srcVal | isGlobal gvii False srcVid = vGlobalArrays srcVval V.! srcVid
               | otherwise = vLocalArrays srcVval V.! getLocalIdx gvii False srcVid

evalExpr :: VarIdInfo -> VarValuation -> Expr -> IntValue
evalExpr _ _ (Literal val) = val
evalExpr gvii vval (Term var)
  | isGlobal gvii True vid = vGlobalScalars vval V.! vid
  | otherwise = vLocalScalars vval V.! getLocalIdx gvii True vid
  where vid = varId var
evalExpr gvii vval (ArrayAccess var idxExpr) =
  arr V.! (fromEnum . B.nat . evalExpr gvii vval $ idxExpr)
  where vid = varId var
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


-- OPM
miniProcSls :: [Prop ExprProp]
miniProcSls = map (Prop . TextProp . T.pack) ["call", "ret", "han", "exc", "stm"]

miniProcPrecRel :: [StructPrecRel ExprProp]
miniProcPrecRel =
  map (\(sl1, sl2, pr) ->
         (Prop . TextProp . T.pack $ sl1, Prop . TextProp . T.pack $ sl2, pr)) precs
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

miniProcAlphabet :: Alphabet ExprProp
miniProcAlphabet = (miniProcSls, miniProcPrecRel)

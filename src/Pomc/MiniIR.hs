{-# LANGUAGE DeriveGeneric #-}

{- |
   Module      : Pomc.MiniIR
   Copyright   : 2020-2023 Michele Chiari
   License     : MIT
   Maintainer  : Michele Chiari
-}

module Pomc.MiniIR ( Program(..)
                   , FunctionSkeleton(..)
                   , Statement(..)
                   , Variable(..)
                   , IntValue
                   , ArrayValue
                   , Expr(..)
                   , LValue(..)
                   , FormalParam(..)
                   , ActualParam(..)
                   , FunctionName
                   , IdType
                   , Type(..)
                   , ExprProp(..)
                   , getExpr
                   , isSigned
                   , isScalar
                   , isArray
                   , typeWidth
                   , arraySize
                   , scalarType
                   , commonType
                   , varWidth
                   , enumerateIntType
                   , VarIdInfo(..)
                   , addVariables
                   , isGlobal
                   , getLocalIdx
                   ) where

import Data.Text (Text)
import qualified Data.Text as T
import Data.Set (Set)
import Data.Maybe (fromMaybe)
import Data.BitVector (BitVector)
import qualified Data.BitVector as B
import Data.Vector (Vector)
import qualified Data.Vector as V
import GHC.Generics (Generic)
import Data.Hashable

-- Intermediate representation for MiniProc programs
type IdType = Int
type FunctionName = Text
data Type = UInt Int
          | SInt Int
          | UIntArray Int Int -- width size
          | SIntArray Int Int -- width size
          deriving (Show, Eq, Ord, Generic)
data Variable = Variable { varId     :: IdType
                         , varName   :: Text
                         , varType   :: Type
                         , varOffset :: IdType
                         } deriving (Show, Eq, Ord, Generic)
type IntValue = BitVector
type ArrayValue = Vector IntValue
data Expr = Literal IntValue
          | Term Variable
          | ArrayAccess Variable Expr
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
          deriving (Eq, Ord)
data LValue = LScalar Variable | LArray Variable Expr deriving (Eq, Ord, Show)
data ActualParam = ActualVal Expr | ActualValRes Variable deriving (Eq, Ord, Show)
data Statement = Assignment LValue Expr
               | Nondeterministic LValue
               | Categorical LValue [Expr] [(Expr, Expr)]
               | Uniform LValue Expr Expr
               | Call FunctionName [ActualParam]
               | Query FunctionName [ActualParam]
               | TryCatch [Statement] [Statement]
               | IfThenElse (Maybe Expr) [Statement] [Statement]
               | While (Maybe Expr) [Statement]
               | Throw (Maybe Expr) deriving Show
data FormalParam = Value Variable | ValueResult Variable deriving (Eq, Ord, Show)
data FunctionSkeleton = FunctionSkeleton { skName    :: FunctionName
                                         , skModules :: [FunctionName]
                                         , skParams  :: [FormalParam]
                                         , skScalars :: Set Variable
                                         , skArrays  :: Set Variable
                                         , skStmts   :: [Statement]
                                         } deriving Show
data Program = Program { pGlobalScalars :: Set Variable
                       , pGlobalArrays  :: Set Variable
                       , pLocalScalars  :: Set Variable
                       , pLocalArrays   :: Set Variable
                       , pSks           :: [FunctionSkeleton]
                       } deriving Show

data ExprProp = TextProp Text | ExprProp (Maybe FunctionName) Expr deriving (Eq, Ord)

instance Hashable Type
instance Hashable Variable
instance Hashable B.BV where
  hashWithSalt s bv = s `hashWithSalt` B.nat bv `hashWithSalt` B.size bv
instance Hashable a => Hashable (Vector a) where
  hashWithSalt s v = V.foldl' hashWithSalt s v

getExpr :: ExprProp -> Expr
getExpr (ExprProp _ e) = e
getExpr _ = error "Unexpected TextProp"

isSigned :: Type -> Bool
isSigned (SInt _) = True
isSigned (SIntArray _ _) = True
isSigned _ = False

isScalar :: Type -> Bool
isScalar (UInt _) = True
isScalar (SInt _) = True
isScalar _ = False

isArray :: Type -> Bool
isArray = not . isScalar

typeWidth :: Type -> Int
typeWidth (UInt w) = w
typeWidth (SInt w) = w
typeWidth (UIntArray w _) = w
typeWidth (SIntArray w _) = w

arraySize :: Type -> Int
arraySize (UIntArray _ s) = s
arraySize (SIntArray _ s) = s
arraySize _ = error "Scalar types do not have a size."

scalarType :: Type -> Type
scalarType (UIntArray w _) = UInt w
scalarType (SIntArray w _) = SInt w
scalarType scalar = scalar

commonType :: Type -> Type -> Type
commonType (UInt w0) (UInt w1) = UInt $ max w0 w1
commonType (UInt w0) (SInt w1) = SInt $ max w0 w1
commonType (SInt w0) (UInt w1) = SInt $ max w0 w1
commonType (SInt w0) (SInt w1) = SInt $ max w0 w1
commonType _ _ = error "Arrays do not have subsuming type."

varWidth :: Variable -> Int
varWidth = typeWidth . varType

enumerateIntType :: Type -> [IntValue]
enumerateIntType ty = B.bitVecs len [(0 :: Integer)..((2 :: Integer)^len-1)]
  where len = typeWidth ty

-- Show instances
instance Show ExprProp where
  show (TextProp t) = T.unpack t
  show (ExprProp s e) = "[" ++ T.unpack (fromMaybe T.empty s) ++ "| " ++ show e ++ "]"

instance Show Expr where
  show expr = case expr of
    Literal v           -> show v
    Term var            -> T.unpack (varName var)
    ArrayAccess var idx -> T.unpack (varName var) ++ "[" ++ show idx ++ "]"
    Not e               -> "! " ++ show e
    And e1 e2           -> showBin "&&" e1 e2
    Or e1 e2            -> showBin "||" e1 e2
    Add e1 e2           -> showBin "+" e1 e2
    Sub e1 e2           -> showBin "-" e1 e2
    Mul e1 e2           -> showBin "*" e1 e2
    UDiv e1 e2          -> showBin "/u" e1 e2
    SDiv e1 e2          -> showBin "/s" e1 e2
    URem e1 e2          -> showBin "%u" e1 e2
    SRem e1 e2          -> showBin "%s" e1 e2
    Eq e1 e2            -> showBin "==" e1 e2
    ULt e1 e2           -> showBin "<" e1 e2
    ULeq e1 e2          -> showBin "<=" e1 e2
    SLt e1 e2           -> showBin "<" e1 e2
    SLeq e1 e2          -> showBin "<=" e1 e2
    UExt w e            -> "(uext " ++ show e ++ " to " ++ show w ++ " bits)"
    SExt w e            -> "(sext " ++ show e ++ " to " ++ show w ++ " bits)"
    Trunc w e           -> "(trunc " ++ show e ++ " to " ++ show w ++ " bits)"
    where showBin op e1 e2 = "(" ++ show e1 ++ " " ++ op ++ " " ++ show e2 ++ ")"


data VarIdInfo = VarIdInfo { scalarOffset :: IdType
                           , arrayOffset  :: IdType
                           , varIds       :: IdType
                           } deriving Show

addVariables :: Bool -> IdType -> VarIdInfo -> (VarIdInfo, [IdType], [IdType])
addVariables scalar n vii =
  let prevIds = if scalar then scalarOffset vii else arrayOffset vii
  in ( if scalar
       then vii { scalarOffset = prevIds + n, varIds = varIds vii + n }
       else vii { arrayOffset = prevIds + n, varIds = varIds vii + n }
     , [prevIds + i | i <- [0..(n - 1)]]
     , [varIds vii + i | i <- [0..(n - 1)]]
     )

isGlobal :: VarIdInfo -> Bool -> IdType -> Bool
isGlobal gvii scalar vid | scalar = vid < scalarOffset gvii
                         | otherwise = vid < arrayOffset gvii

getLocalIdx :: VarIdInfo -> Bool -> IdType -> Int
getLocalIdx gvii scalar vid | scalar = vid - scalarOffset gvii
                            | otherwise = vid - arrayOffset gvii

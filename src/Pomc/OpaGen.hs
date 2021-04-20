{- |
   Module      : Pomc.OpaGen
   Copyright   : 2020-2021 Michele Chiari
   License     : MIT
   Maintainer  : Michele Chiari
-}

module Pomc.OpaGen ( printFunctions
                   , genOpa
                   , genBench
                   ) where

import Pomc.Prop (Prop(..))
import Pomc.ModelChecker (ExplicitOpa(..))
import Pomc.MiniProc (FunctionSkeleton(..), Statement(..), FunctionName, skeletonsToOpa)

import System.Random
import System.IO
import System.FilePath ((</>))
import Control.Monad (foldM)
import Data.Set (Set)
import qualified Data.Set as S
import qualified Data.Text as T


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
                    -> Int
                    -> FunctionName
                    -> (FunctionSkeleton, g)
genFunctionSkeleton gen fs maxCalls maxDepth fname =
  let (statements, gen') = genBlock gen fs maxCalls maxDepth [genTryCatch, genIfThenElse, genThrow]
  in (FunctionSkeleton fname [] statements, gen')

genBlock :: RandomGen g
         => g
         -> [FunctionName]
         -> Int
         -> Int
         -> [g -> [FunctionName] -> Int -> Int -> (Statement, g)]
         -> ([Statement], g)
genBlock gen fs maxCalls maxDepth stmtGens =
  foldl createStatements ([], gen') stmtIndices
  where (stmtIndices, gen') = genIndices gen maxCalls (length fs + length stmtGens - 1)
        createStatements (stmts, oldGen) idx
          | idx < length fs || maxDepth == 0 = ((Call (fs !! (idx `mod` length fs))) : stmts, oldGen)
          | otherwise = let (tcStmt, newGen) = (stmtGens !! (idx - length fs)) oldGen fs maxCalls (maxDepth-1)
                        in (tcStmt : stmts, newGen)

genTryCatch :: RandomGen g => g -> [FunctionName] -> Int -> Int -> (Statement, g)
genTryCatch gen fs maxCalls maxDepth =
  let (try, gen') = genBlock gen fs maxCalls maxDepth [genIfThenElse, genThrow]
      (catch, gen'') = genBlock gen' fs maxCalls maxDepth [genIfThenElse]
  in (TryCatch try catch, gen'')

genIfThenElse :: RandomGen g => g -> [FunctionName] -> Int -> Int -> (Statement, g)
genIfThenElse gen fs maxCalls maxDepth =
  let (thenBlock, gen') = genBlock gen fs maxCalls maxDepth [genTryCatch, genIfThenElse, genThrow]
      (elseBlock, gen'') = genBlock gen' fs maxCalls maxDepth [genTryCatch, genIfThenElse, genThrow]
  in (IfThenElse Nothing thenBlock elseBlock, gen'')

genThrow :: RandomGen g => g -> [FunctionName] -> Int -> Int -> (Statement, g)
genThrow gen _ _ _ = (Throw, gen)

genSkeletons :: RandomGen g => g -> Int -> Int -> Int -> ([FunctionSkeleton], g)
genSkeletons gen nf maxCalls maxDepth = foldl foldSkeletons ([], gen) fs
  where fs = map (\n -> T.pack $ "p" ++ show n) [nf, nf-1 .. 0]
        foldSkeletons (sks, oldGen) fname =
          let (sk, newGen) = genFunctionSkeleton oldGen fs maxCalls maxDepth fname
          in (sk : sks, newGen)


printFunctions :: Int -> Int -> Int -> IO ()
printFunctions nf maxCalls maxDepth = do
  gen <- newStdGen
  (skeletons, _) <- return $ genSkeletons gen nf maxCalls maxDepth
  putStrLn $ show skeletons
  let opa = skeletonsToOpa skeletons
  putStrLn $ show opa
  hWriteOpa opa stdout

genOpa :: String -> Int -> Int -> Int -> IO ()
genOpa file nf maxCalls maxDepth = do
  gen <- newStdGen
  (skeletons, _) <- return $ genSkeletons gen nf maxCalls maxDepth
  opa <- return $ skeletonsToOpa skeletons
  withFile file WriteMode (hWriteOpa opa)

genBench :: String -> IO ()
genBench dir = do
  gen <- newStdGen
  _ <- foldM genSomeOpa gen [4..36]
  return ()
  where genSomeOpa gen maxCalls = foldM genSingleOpa gen [1..8]
          where genSingleOpa :: RandomGen g => g -> Int -> IO (g)
                genSingleOpa gen' n = do
                  (skeletons, gen'') <- return $ genSkeletons gen' (maxCalls `div` 4) maxCalls 4
                  opa <- return $ skeletonsToOpa skeletons
                  withFile (dir </> (show maxCalls ++ "-" ++ show n ++ ".pomc"))
                    WriteMode (hWriteOpa opa)
                  return gen''


hWriteOpa :: (Show s, Show a) => ExplicitOpa s a -> Handle -> IO ()
hWriteOpa opa h = do
  hPutStrLn h evalHeader
  hPutStrLn h $ "  initials = " ++ formatList (map show $ initials opa) ++ ";"
  hPutStrLn h $ "  finals = " ++ formatList (map show $ finals opa) ++ ";"
  hPutStrLn h $ "  deltaPush = " ++ formatDeltaInput (deltaPush opa) ++ ";"
  hPutStrLn h $ "  deltaShift = " ++ formatDeltaInput (deltaShift opa) ++ ";"
  hPutStrLn h $ "  deltaPop = " ++ formatDeltaPop (deltaPop opa) ++ ";"

formatList :: [String] -> String
formatList [] = ""
formatList (x : []) = x
formatList (x : xs) = foldl (\acc y -> acc ++ " " ++ y) ("(" ++ x) xs ++ ")"

formatDeltaInput :: (Show s, Show a) => [(s, Set (Prop a), [s])] -> String
formatDeltaInput di = formatDeltaList $ map formatRel di
  where formatRel (q, b, ps) =
          "(" ++ show q ++ ", " ++ formatPropSet b ++ ", " ++ formatStateList ps ++ ")"
        formatPropSet b = formatList $ map unProp (S.toList b)

        unProp (Prop p) = show p
        unProp End = "#"

formatDeltaPop :: (Show s) => [(s, s, [s])] -> String
formatDeltaPop dp = formatDeltaList $ map formatRel dp
  where formatRel (q, r, ps) =
          "(" ++ show q ++ ", " ++ show r ++ ", " ++ formatStateList ps ++ ")"

formatDeltaList :: [String] -> String
formatDeltaList [] = ""
formatDeltaList (x : []) = x
formatDeltaList (x : xs) = foldl (\acc rel -> acc ++ ", " ++ rel) x xs

formatStateList :: (Show s) => [s] -> String
formatStateList sl = formatList $ map show sl

evalHeader :: String
evalHeader =
  "prec = Mcall;\n\
  \\n\
  \formulas = PNd (PNd (call And (XNu exc))),\
  \\n           PNd (han And (XNd (exc And (XBu call)))),\
  \\n           G (exc --> XBu call),\
  \\n           T Ud exc,\
  \\n           F (HNd p1),\
  \\n           F (HBd p2),\
  \\n           G ((call And p0) --> (~ p1) HUu p2),\
  \\n           F (HNu p1),\
  \\n           F (HBu p1),\
  \\n           F (p0 And (call HUu p1)),\
  \\n           F (p1 And (call HSu p0)),\
  \\n           G (call --> XNd ret),\
  \\n           G (call --> Not (PNu exc)),\
  \\n           G ((call And p0) --> ~ (PNu exc Or XNu exc)),\
  \\n           G (exc --> ~ (PBu (call And p0) Or XBu (call And p0))),\
  \\n           G ((call And p2 And (call Sd (call And p1))) --> (PNu exc Or XNu exc)),\
  \\n           G (han --> XNu ret),\
  \\n           G (call And p2 --> (T Uu (exc And XBd han))),\
  \\n           call Ud (ret And p1),\
  \\n           XNd (call And ((call Or exc) Su p0));\
  \\n\
  \\nopa:"

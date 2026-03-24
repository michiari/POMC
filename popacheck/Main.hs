{-# LANGUAGE DeriveDataTypeable #-}
{-# OPTIONS_GHC -fno-cse #-}
{- |
   Module      : Main
   Copyright   : 2020-2025 Michele Chiari
   License     : MIT
   Maintainer  : Michele Chiari
-}

module Main (main) where

import Pomc.Prob.ProbModelChecker (programTermination, qualitativeModelCheckProgram, quantitativeModelCheckProgram, exportMarkovChain)
import Pomc.Prob.ProbUtils (Solver(..), Stats(..), Update(..), TermResult(..), Distr(..))
import Pomc.Parse.Parser (checkRequestP, spaceP, CheckRequest(..), preprocess)
import Pomc.TimeUtils (timeAction, timeToString)
import Pomc.LogUtils (LogLevel(..), selectLogVerbosity)

import Prelude hiding (readFile)
import Numeric (showEFloat, showFFloat)

import System.Exit
import System.FilePath
import System.Console.CmdArgs
import Control.Monad (when)
import Text.Megaparsec
import Data.Text.IO (readFile)

data POPACheckArgs = POPACheckArgs
  { noovi :: Bool
  , gauss :: Bool
  , stats :: Bool
  , verbose :: Int
  , maxDepth :: Int
  , fileName :: FilePath
  } deriving (Data, Typeable, Show, Eq)

popacheckArgs :: POPACheckArgs
popacheckArgs = POPACheckArgs
  { noovi = False &= help "Use z3 instead of Optimistic Value Iteration for computing upper bounds to the Least Fixed Point solution of the equation systems for pOPA's termination probabilities."
  , gauss = False &= help "Use Gauss-Seidel Value Iteration instead of Newton's method to iterate the Least Fixed point solution of the equation systems for pOPA's termination probabilities and for quantitative model checking."
  , stats = False &= help "Print detailed results containing technical stats."
  , verbose = 0 &= help "Print more info about model checking progress. 0 = no logging (default), 1 = show info, 2 = debug mode"
  , maxDepth = 100 &= help "Max stack depth when exporting a Markov Chain representation of the input program with unfolded stack (default = 100) [test feature only]"
  , fileName = def &= args &= typFile
  }
  &= program "popacheck"
  &= summary "POPACheck v3.1.0"
  &= details [ "Only one input file can be specified." ]

main :: IO ()
main = do
  pargs <- cmdArgs popacheckArgs
  let updateStrategy
        | gauss pargs = GS
        | otherwise = Newton
      probSolver
        | noovi pargs = SMTWithHints updateStrategy
        | otherwise = OVI updateStrategy
      depth = maxDepth pargs
      fname = fileName pargs
      printStats = stats pargs
      logLevel = case verbose pargs of
        0 -> Nothing
        1 -> Just LevelInfo
        _ -> Just LevelDebug

  fcontent <- readFile fname
  prepcontent <- preprocess fname fcontent

  creq <- case parse (spaceP *> checkRequestP <* eof) fname prepcontent of
            Left  errBundle -> die (errorBundlePretty errBundle)
            Right creq      -> return creq
  totalTime <- case creq of
    ProbTermRequest prog -> runProbTerm printStats logLevel probSolver prog
    ProbCheckRequest phi prog False -> runQualProbCheck printStats logLevel probSolver phi prog
    ProbCheckRequest phi prog True -> runQuantProbCheck printStats logLevel probSolver phi prog
    ProbUnfoldRequest phi prog -> runUnfoldAndExport logLevel phi prog depth fname
    _ -> die "POPACheck only supports probabilistic queries. Please use the pomc executable for non-probabilistic model checking, or popalyzer for inference queries."

  putStrLn ("\nTotal elapsed time: " ++ timeToString totalTime ++
            " (" ++ showEFloat (Just 4) totalTime " s)")
  where
    runProbTerm printStats logLevel solver prog = do
      putStrLn "Probabilistic Termination Checking"
      when printStats $ putStrLn $ "Query: ApproxSingleQuery " ++ (show solver)
      putStr "Result: "
      ((tres@(ApproxSingleResult (lb, ub)), stats, _), time) <- timeAction fst3
        $ selectLogVerbosity logLevel
        $ programTermination solver prog
      if printStats
        then do
        putStr $ show tres
        putStrLn $ concat
          [ "\nFloating Point Result:  "
          , show (fromRational lb :: Double, fromRational ub :: Double)
          , "\nElapsed time: "
          , timeToString time, " (total), "
          , showEFloat (Just 4) (upperBoundTime stats) " s (upper bounds), "
          , showEFloat (Just 4) (pastTime stats) " s (PAST certificates), "
          , showEFloat (Just 4) (gGraphTime stats) " s (graph analysis)."
          , "\nInput pOPA state count: ", show $ popaStatesCount stats
          , "\nSupport graph size: ", show $ suppGraphLen stats
          -- termination probabilities
          , "\nSCC count in the support graph: ", show $ sccCountSuppGraph stats
          , "\nSize of the largest SCC in the support graph: ", show $ largestSCCSuppGraphSize stats
          , "\nEquations solved for termination probabilities: ", show $ equationsCount stats
          , "\nNon-trivial equations solved for termination probabilities: ", show $ nonTrivialEquationsCount stats
          , "\nSCC count in the equation system for termination probabilities: ", show $ sccCountEqSys stats
          , "\nSize of the largest SCC in the equation system for termination probabilities: ", show $ largestSCCSuppGraphSize stats
          ]
        else putStrLn $ concat
             [ "\n  Lower bound: "
             , showFFloat (Just 4) (fromRational lb :: Double) ""
             , "\n  Upper bound: "
             , showFFloat (Just 4) (fromRational ub :: Double) ""
             ]
      return time

    runQualProbCheck printStats logLevel solver phi prog = do
      putStr (concat [ "Qualitative Probabilistic Model Checking\nQuery: ", show phi
                     , "\nResult: "
                     ])
      ((tres, stats, _), time) <- timeAction fst3 $ selectLogVerbosity logLevel
        $ qualitativeModelCheckProgram solver phi prog
      putStr $ show tres
      when (not printStats && tres) $ putStr " (almost surely)"
      if printStats
        then putStrLn $ concat
             [ "\nElapsed time: "
             , timeToString time, " (total), "
             , showEFloat (Just 4) (upperBoundTime stats) " s (upper bounds), "
             , showEFloat (Just 4) (pastTime stats) " s (PAST certificates), "
             , showEFloat (Just 4) (gGraphTime stats) " s (graph analysis)."
             , "\nInput pOPA state count: ", show $ popaStatesCount stats
             , "\nSupport graph size: ", show $ suppGraphLen stats
             -- termination probabilities
             , "\nSCC count in the support graph: ", show $ sccCountSuppGraph stats
             , "\nSize of the largest SCC in the support graph: ", show $ largestSCCSuppGraphSize stats
             , "\nEquations solved for termination probabilities: ", show $ equationsCount stats
             , "\nNon-trivial equations solved for termination probabilities: ", show $ nonTrivialEquationsCount stats
             , "\nSCC count in the equation system for termination probabilities: ", show $ sccCountEqSys stats
             , "\nSize of the largest SCC in the equation system for termination probabilities: ", show $ largestSCCSuppGraphSize stats
             -- qualitative model checking
             , "\nSize of (the explored portion of) graph G: ", show $ gGraphSize stats -- we may abort exploration if we have already established True.
             ]
        else putChar '\n'
      return time

    runQuantProbCheck printStats logLevel solver phi prog = do
      putStr (concat [ "Quantitative Probabilistic Model Checking\nQuery: ", show phi
                     , "\nResult: "
                     ])
      ((tres@(lb,ub), stats, _), time) <- timeAction fst3 $ selectLogVerbosity logLevel
        $ quantitativeModelCheckProgram solver phi prog
      if printStats
        then do
        putStr $ show tres
        putStrLn $ concat
          [ "\nFloating Point Result:  "
          , show (fromRational lb :: Double, fromRational ub :: Double)
          , "\nElapsed time: "
          , timeToString time, " (total), "
          , showEFloat (Just 4) (upperBoundTime stats) " s (upper bounds), "
          , showEFloat (Just 4) (pastTime stats) " s (PAST certificates), "
          , showEFloat (Just 4) (gGraphTime stats) " s (graph analysis),"
          , showEFloat (Just 4) (quantWeightTime stats) " s (upper bounds with OVI for quant MC),"
          , showEFloat (Just 4) (quantSolTime stats) " s (eq system for quant MC)."
          , "\nInput pOPA state count: ", show $ popaStatesCount stats
          , "\nSupport graph size: ", show $ suppGraphLen stats
          -- termination probabilities
          , "\nSCC count in the support graph: ", show $ sccCountSuppGraph stats
          , "\nSize of the largest SCC in the support graph: ", show $ largestSCCSuppGraphSize stats
          , "\nEquations solved for termination probabilities: ", show $ equationsCount stats
          , "\nNon-trivial equations solved for termination probabilities: ", show $ nonTrivialEquationsCount stats
          , "\nSCC count in the equation system for termination probabilities: ", show $ sccCountEqSys stats
          , "\nSize of the largest SCC in the equation system for termination probabilities: ", show $ largestSCCSuppGraphSize stats
          -- qualitative model checking
          , "\nSize of graph G: ", show $ gGraphSize stats
          -- quantitative mc
          , "\nSCC count in the support graph of the cross product for quantitative mc: ", show $ sccCountSuppGraphQuant stats
          , "\nSize of the largest SCC in the support graph of the cross product for quantitative mc: ", show $ largestSCCSuppSizeQuant stats
          , "\nEquations solved for quant mc: ", show $ equationsCountQuant stats
          , "\nNon-trivial equations solved for quant mc: ", show $ nonTrivialEquationsCountQuant stats
          , "\nSCC count in the equation system for quant mc weight computation: ", show $ sccCountEqSysQuant stats
          , "\nSize of the largest SCC in the equation system for quant mc weight computation: ", show $ largestSCCEqSysSizeQuant stats
          ]
        else putStrLn $ concat
             [ "\n  Lower bound: "
             , showFFloat (Just 4) (fromRational lb :: Double) ""
             , "\n  Upper bound: "
             , showFFloat (Just 4) (fromRational ub :: Double) ""
             ]
      return time

    runUnfoldAndExport logLevel phi prog depth fname = do
      putStr (concat [ "\nUnfolding the stack into this model and exporting a Markov Chain [max stack depth = ", show depth, "]",
                       "\nQuery: ", show phi
                     ])
      (_, time) <- timeAction id $ selectLogVerbosity logLevel
        $ exportMarkovChain phi prog depth (replaceExtension fname ".tra") (replaceExtension fname ".lab")
      putStr "\nFiles exported correctly."
      return time

    fst3 (a, _, _) = a

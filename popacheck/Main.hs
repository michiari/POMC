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
import Pomc.Prob.ProbUtils (Solver(..), Stats(..))
import Pomc.Parse.Parser (checkRequestP, spaceP, CheckRequest(..), preprocess)
import Pomc.TimeUtils (timeAction, timeToString)
import Pomc.LogUtils (LogLevel(..), selectLogVerbosity)

import Prelude hiding (readFile)
import Numeric (showEFloat)

import System.Exit
import System.FilePath
import System.Console.CmdArgs
import Text.Megaparsec
import Data.Text.IO (readFile)

data POPACheckArgs = POPACheckArgs
  { noovi :: Bool
  , newton :: Bool
  , verbose :: Int
  , maxDepth :: Int
  , fileName :: FilePath
  } deriving (Data, Typeable, Show, Eq)

popacheckArgs :: POPACheckArgs
popacheckArgs = POPACheckArgs
  { noovi = False &= help "Use z3 instead of Optimistic Value Iteration for computing upper bounds to the Least Fixed Point solution of the equation systems for pOPA's termination probabilities"
  , newton = False &= help "Use Newton's method instead of Gauss-Seidel Value Iteration to iterate the Least Fixed point solution of the equation systems for pOPA's termination probabilities and for quantitative model checking"
  , verbose = 0 &= help "Print more info about model checking progress. 0 = no logging (default), 1 = show info, 2 = debug mode"
  , maxDepth = 100 &= help "Max stack depth when exporting a Markov Chain representation of the input program with unfolded stack (default = 100) [test feature only]"
  , fileName = def &= args &= typFile -- &= help "Input file"
  }
  &= summary "POPACheck v3.0.0"
  &= details [ "Only one input file can be specified." ]

main :: IO ()
main = do
  pargs <- cmdArgs popacheckArgs
  let probSolver | noovi pargs = SMTWithHints
                 | newton pargs = OVINewton
                 | otherwise = OVIGS
      depth = maxDepth pargs
      fname = fileName pargs
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
    ProbTermRequest _ prog -> runProbTerm logLevel probSolver prog
    ProbCheckRequest phi prog False -> runQualProbCheck logLevel probSolver phi prog
    ProbCheckRequest phi prog True -> runQuantProbCheck logLevel probSolver phi prog
    ProbUnfoldRequest phi prog -> runUnfoldAndExport logLevel phi prog depth fname
    _ -> die "POPACheck only supports probabilistic queries. Please use the pomc executable for non-probabilistic model checking."

  putStrLn ("\n\nTotal elapsed time: " ++ timeToString totalTime ++
            " (" ++ showEFloat (Just 4) totalTime " s)")
  where
    runProbTerm logLevel solver prog = do
      putStr (concat [ "\nProbabilistic Termination Checking\nQuery: ApproxSingleQuery ", show solver
                     , "\nResult:  "
                     ])
      ((tres, stats, _), time) <- timeAction fst3 $ selectLogVerbosity logLevel
        $ programTermination solver prog
      putStr $ show tres
      putStrLn (concat [ "\nElapsed time: "
                      , timeToString time, " (total), "
                      , showEFloat (Just 4) (upperBoundTime stats) " s (upper bounds), "
                      , showEFloat (Just 4) (pastTime stats) " s (PAST certificates), "
                      , showEFloat (Just 4) (gGraphTime stats) " s (graph analysis)."
                      , "\nInput pOPA state count: ", show $ popaStatesCount stats
                      , "\nSupport graph size: ", show $ suppGraphLen stats
                      , "\nEquations solved for termination probabilities: ", show $ equationsCount stats
                      , "\nNon-trivial equations solved for termination probabilities: ", show $ nonTrivialEquationsCount stats
                      , "\nSCC count in the support graph: ", show $ sccCount stats
                      , "\nSize of the largest SCC in the support graph: ", show $ largestSCCSemiconfsCount stats
                      , "\nLargest number of non trivial equations in an SCC in the Support Graph: ", show $ largestSCCNonTrivialEqsCount stats
                      ])
      return time

    runQualProbCheck logLevel solver phi prog = do
      putStr (concat [ "\nQualitative Probabilistic Model Checking\nQuery: ", show phi
                     , "\nResult:  "
                     ])
      ((tres, stats, _), time) <- timeAction fst3 $ selectLogVerbosity logLevel
        $ qualitativeModelCheckProgram solver phi prog
      putStr $ show tres
      putStrLn (concat [ "\nElapsed time: "
                       , timeToString time, " (total), "
                       , showEFloat (Just 4) (upperBoundTime stats) " s (upper bounds), "
                       , showEFloat (Just 4) (pastTime stats) " s (PAST certificates), "
                       , showEFloat (Just 4) (gGraphTime stats) " s (graph analysis)."
                       , "\nInput pOPA state count: ", show $ popaStatesCount stats
                       , "\nSupport graph size: ", show $ suppGraphLen stats
                       , "\nEquations solved for termination probabilities: ", show $ equationsCount stats
                       , "\nNon-trivial equations solved for termination probabilities: ", show $ nonTrivialEquationsCount stats
                       , "\nSCC count in the support graph: ", show $ sccCount stats
                       , "\nSize of the largest SCC in the support graph: ", show $ largestSCCSemiconfsCount stats
                       , "\nLargest number of non trivial equations in an SCC in the Support Graph: ", show $ largestSCCNonTrivialEqsCount stats
                       , "\nSize of graph G: ", show $ gGraphSize stats
                       ])
      return time

    runQuantProbCheck logLevel solver phi prog = do
      putStr (concat [ "\nQuantitative Probabilistic Model Checking\nQuery: ", show phi
                     , "\nResult:  "
                     ])
      ((tres@(lb,ub), stats, _), time) <- timeAction fst3 $ selectLogVerbosity logLevel
        $ quantitativeModelCheckProgram solver phi prog
      putStr $ show tres
      putStr ("\nFloating Point Result:  " ++ show (fromRational lb :: Double, fromRational ub :: Double))
      putStrLn (concat [ "\nElapsed time: "
                       , timeToString time, " (total), "
                       , showEFloat (Just 4) (upperBoundTime stats) " s (upper bounds), "
                       , showEFloat (Just 4) (pastTime stats) " s (PAST certificates), "
                       , showEFloat (Just 4) (gGraphTime stats) " s (graph analysis),"
                       , showEFloat (Just 4) (quantWeightTime stats) " s (upper bounds with OVI for quant MC),"
                       , showEFloat (Just 4) (quantSolTime stats) " s (eq system for quant MC)."
                       , "\nInput pOPA state count: ", show $ popaStatesCount stats
                       , "\nSupport graph size: ", show $ suppGraphLen stats
                       , "\nEquations solved for termination probabilities: ", show $ equationsCount stats
                       , "\nNon-trivial equations solved for termination probabilities: ", show $ nonTrivialEquationsCount stats
                       , "\nSCC count in the support graph: ", show $ sccCount stats
                       , "\nSize of the largest SCC in the support graph: ", show $ largestSCCSemiconfsCount stats
                       , "\nLargest number of non trivial equations in an SCC in the Support Graph: ", show $ largestSCCNonTrivialEqsCount stats
                       , "\nSize of graph G: ", show $ gGraphSize stats
                       --
                       , "\nEquations solved for quant mc: ", show $ equationsCountQuant stats
                       , "\nNon-trivial equations solved for quant mc: ", show $ nonTrivialEquationsCountQuant stats
                       , "\nSCC count in quant mc weight computation: ", show $ sccCountQuant stats
                       , "\nSize of the largest SCC in quant mc weight computation: ", show $ largestSCCSemiconfsCountQuant stats
                       , "\nLargest number of non trivial equations in an SCC in quant mc weight computation: ", show $ largestSCCNonTrivialEqsCountQuant stats
                       ])
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

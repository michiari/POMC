{-# LANGUAGE DeriveDataTypeable #-}
{-# OPTIONS_GHC -fno-cse #-}
{- |
   Module      : Main
   Copyright   : 2020-2025 Francesco Pontiggia
   License     : MIT
   Maintainer  : Francesco Pontiggia
-}

module Main (main) where

import Pomc.Prob.POPAlyzer (infer)
import Pomc.Prob.ProbUtils (Stats(..), Update(..), Distr(..))
import Pomc.Parse.Parser (checkRequestP, spaceP, CheckRequest(..), preprocess)
import Pomc.TimeUtils (timeAction, timeToString)
import Pomc.LogUtils (LogLevel(..), selectLogVerbosity)
import Pomc.Prob.ProbUtils(defaultEps)

import Prelude hiding (readFile)
import Numeric (showEFloat, showFFloat)

import System.Exit
import System.FilePath
import System.Console.CmdArgs
import Control.Monad (when)
import Text.Megaparsec
import Data.Text.IO (readFile)

data POPAlyzerArgs = POPAlyzerArgs
  { gauss :: Bool
  , stats :: Bool
  , verbose :: Int
  , eps :: Double
  , fileName :: FilePath
  } deriving (Data, Typeable, Show, Eq)

popalyzerArgs :: POPAlyzerArgs
popalyzerArgs = POPAlyzerArgs
  { gauss = False &= help "Use Gauss-Seidel Value Iteration instead of Newton's method to iterate the Least Fixed point solution of the equation systems."
  , stats = False &= help "Print detailed results containing technical stats."
  , verbose = 0 &= help "Print more info about model checking progress. 0 = no logging (default), 1 = show info, 2 = debug mode"
  , eps = defaultEps &= help ("Stopping criterion for iterative numerical methods: bound on the absolute difference between consecutive approximations. Default: " ++ show defaultEps)
  , fileName = def &= args &= typFile
  }
  &= program "popalyzer"
  &= summary "POPAlyzer v3.1.0"
  &= details [ "Only one input file can be specified." ]

main :: IO ()
main = do
  pargs <- cmdArgs popalyzerArgs
  let updateStrategy
        | gauss pargs = GS
        | otherwise = Newton
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
    ProbInferenceRequest prog expr -> runProbInference printStats logLevel updateStrategy prog (eps pargs) expr
    _ -> die "POPAlyzer only supports inference queries. Please use the pomc or the popacheck executables for model checking."

  putStrLn ("\nTotal elapsed time: " ++ timeToString totalTime ++
            " (" ++ showEFloat (Just 4) totalTime " s)")
  where
    runProbInference printStats logLevel strat prog eps expr = do
      putStrLn "Posterior Distribution Inference Query"
      when printStats $ putStrLn $ "Query: InferenceQuery " ++ (show strat)
      putStr "Result: "
      ((tres@(Distr lb, Distr ub), stats, _), time) <- timeAction fst3
        $ selectLogVerbosity logLevel
        $ infer strat prog eps expr
      if printStats
        then do
        putStr $ show tres
        putStrLn $ concat
          [ "\nFloating Point Result:\n Lower bounds Distribution:"
          , concatMap (\(e, p) -> "\nP(" ++ show e ++ ") = " ++ (showFFloat (Just 4) (fromRational p :: Double) "") ++ ";") lb
          , "\n Upper bounds Distribution:"
          , concatMap (\(e, p) -> "\nP(" ++ show e ++ ") = " ++ (showFFloat (Just 4) (fromRational p :: Double) "") ++ ";") ub
          , "\nElapsed time: "
          , timeToString time, " (total), "
          , showEFloat (Just 4) (upperBoundTime stats) " s (upper bounds), "
          , showEFloat (Just 4) (pastTime stats) " s (PAST certificates), "
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
             [ "\n Lower bounds Distribution:"
             , concatMap (\(e, p) -> "\nP(" ++ show e ++ ") = " ++ (showFFloat (Just 4) (fromRational p :: Double) "") ++ ";") lb
             , "\n Upper bounds Distribution:"
             , concatMap (\(e, p) -> "\nP(" ++ show e ++ ") = " ++ (showFFloat (Just 4) (fromRational p :: Double) "") ++ ";") ub
             ]
      return time

    fst3 (a, _, _) = a

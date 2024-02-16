{-# LANGUAGE DeriveDataTypeable #-}
{-# OPTIONS_GHC -fno-cse #-}
{- |
   Module      : Main
   Copyright   : 2020-2023 Davide Bergamaschi, Michele Chiari
   License     : MIT
   Maintainer  : Michele Chiari
-}

module Main (main) where

import Pomc.Check (fastcheckGen)
import Pomc.ModelChecker (modelCheckExplicitGen, modelCheckProgram, countStates)
import Pomc.Prob.ProbModelChecker (programTermination, qualitativeModelCheckProgram, quantitativeModelCheckProgram)
import Pomc.Prob.ProbUtils (Solver(..), Stats(..))
import Pomc.Parse.Parser (checkRequestP, spaceP, CheckRequest(..), includeP)
import Pomc.Prec (Prec(..))
import Pomc.Prop (Prop(..))
import Pomc.TimeUtils (timeAction, timeFunApp, timeToString)
import Pomc.LogUtils (LogLevel(..), selectLogVerbosity)

import Prelude hiding (readFile)
import Numeric (showEFloat)

import System.Exit
import System.FilePath
import System.Console.CmdArgs

import Text.Megaparsec
import Data.Text.IO (readFile)
import qualified Data.Text as T

import Data.List (intersperse)

import qualified Data.Set as S

import Control.Monad

data PomcArgs = PomcArgs
  { finite :: Bool
  , infinite :: Bool
  , noovi :: Bool
  , verbose :: Int
  , fileName :: FilePath
  } deriving (Data,Typeable,Show,Eq)

pomcArgs :: PomcArgs
pomcArgs = PomcArgs
  { finite = False &= help "Use finite-word semantics"
  , infinite = False &= help "Use infinite-word (omega) semantics (default)"
  , noovi = False &= help "Use z3 instead of Optimistic Value Iteration for probabilistic model checking"
  , verbose = 0 &= help "Print more info about model checking progress. 0 = no logging (default), 1 = show info, 2 = debug mode"
  , fileName = def &= args &= typFile -- &= help "Input file"
  }
  &= summary "POMC v2.1.0"
  &= details [ "Only one input file can be specified."
             , "--finite and --infinite cannot be specified together."
             ]

main :: IO ()
main = do
  pargs <- cmdArgs pomcArgs
  if infinite pargs && finite pargs
    then die "--finite and --infinite cannot be specified together."
    else return ()
  let isOmega = not $ finite pargs
      probSolver | noovi pargs = SMTWithHints
                 | otherwise = OVI
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
    ExplCheckRequest phis rawPrecRels maybeStrings maybeOpa -> do
      let precRels = addEndPrec rawPrecRels
      stringTimes <- case maybeStrings of
        Just strings -> forM [(phi, s) | phi <- phis, s <- strings]
          (uncurry $ runString precRels)
        Nothing -> return []

      mcTimes <- case maybeOpa of
        Just opa -> forM phis (runMC isOmega opa)
        Nothing -> return []

      return $ sum stringTimes + sum mcTimes

    ProgCheckRequest phis prog -> sum <$> forM phis (runProg isOmega prog)
    ProbTermRequest _ prog -> runProbTerm logLevel probSolver prog
    ProbCheckRequest phi prog False -> runQualProbCheck logLevel probSolver phi prog
    ProbCheckRequest phi prog True -> runQuantProbCheck logLevel probSolver phi prog

  putStrLn ("\n\nTotal elapsed time: " ++ timeToString totalTime ++
            " (" ++ showEFloat (Just 4) totalTime " s)")
  where
    runString precRels phi s = do
      putStr (concat [ "\nFormula: ", show phi
                     , "\nString:  ", showstring s
                     , "\nResult:  "
                     ])
      (sat, time) <- timeFunApp id (fastcheckGen phi precRels) s
      putStr $ show sat
      putStrLn (concat ["\nElapsed time: ", timeToString time])
      return time

    runMC isOmega opa phi = do
      putStr (concat [ "\nModel Checking\nFormula: ", show phi
                     , "\nInput OPA state count: ", show $ countStates opa
                     , "\nResult:  "
                     ])
      ((sat, trace), time) <- timeFunApp fst (modelCheckExplicitGen isOmega phi) opa
      putStr $ show sat
      unless sat $ putStr $ "\nCounterexample: " ++ showPrettyTrace "..." T.unpack trace
      putStrLn (concat ["\nElapsed time: ", timeToString time])
      return time

    runProg isOmega prog phi = do
      putStr (concat [ "\nModel Checking\nFormula: ", show phi
                     , "\nResult:  "
                     ])
      ((sat, trace), time) <- timeFunApp fst (modelCheckProgram isOmega phi) prog
      putStr $ show sat
      unless sat $ putStr $ "\nCounterexample: " ++ showPrettyTrace "..." show trace
      putStrLn (concat ["\nElapsed time: ", timeToString time])
      return time

    runProbTerm logLevel solver prog = do
      putStr (concat [ "\nProbabilistic Termination Checking\nQuery: ApproxSingleQuery ", show solver
                     , "\nResult:  "
                     ])
      ((tres, _, _), time) <- timeAction fst3 $ selectLogVerbosity logLevel
        $ programTermination solver prog
      putStr $ show tres
      putStrLn (concat ["\nElapsed time: ", timeToString time])
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
                       , "\nNon-trivial equations solved for termination probabilities: ", show $ nonTrivialEquations stats
                       , "\nSCC count in the support graph: ", show $ sccCount stats
                       , "\nSize of the largest SCC in the support graph: ", show $ largestSCCSemiconfsCount stats
                       , "\nLargest number of equations in an SCC in the Support Graph: ", show $ largestSCCEqsCount stats
                       ])
      return time

    runQuantProbCheck logLevel solver phi prog = do
      putStr (concat [ "\nQuantitative Probabilistic Model Checking\nQuery: ", show phi
                     , "\nResult:  "
                     ])
      ((tres, stats, _), time) <- timeAction fst3 $ selectLogVerbosity logLevel
        $ quantitativeModelCheckProgram solver phi prog
      putStr $ show tres
      putStrLn (concat [ "\nElapsed time: "
                       , timeToString time, " (total), "
                       , showEFloat (Just 4) (upperBoundTime stats) " (upper bounds), "
                       , showEFloat (Just 4) (pastTime stats) " (PAST certificates), "
                       , showEFloat (Just 4) (gGraphTime stats) " s (graph analysis),"
                       , showEFloat (Just 4) (quantWeightTime stats) " (weights for quant MC),"
                       , showEFloat (Just 4) (quantSolTime stats) " (eq system for quant MC)."
                       , "\nInput pOPA state count: ", show $ popaStatesCount stats
                       , "\nSupport graph size: ", show $ suppGraphLen stats
                       , "\nNon-trivial equations solved for termination probabilities: ", show $ nonTrivialEquations stats
                       , "\nSCC count in the support graph: ", show $ sccCount stats
                       , "\nSize of the largest SCC in the support graph: ", show $ largestSCCSemiconfsCount stats
                       , "\nLargest number of equations in an SCC in the Support Graph: ", show $ largestSCCEqsCount stats
                       ])
      return time

    fst3 (a, _, _) = a

    addEndPrec precRels = noEndPR
                          ++ map (\p -> (End, p, Yield)) sl
                          ++ map (\p -> (p, End, Take)) sl
      where sl = S.toList $ S.fromList $ concatMap (\(sl1, sl2, _) -> [sl1, sl2]) noEndPR
            noEndPR = filter (\(p1, p2, _) -> p1 /= End && p2 /= End) precRels

    showp showf prop = case prop of Prop p -> showf p
                                    End    -> "#"
    showpset pset = let showpset' = concat . intersperse " " . map (showp show) . S.toList
                    in concat ["(", showpset' pset, ")"]
    showstring = concat . intersperse " " . map showpset

    showPrettyTrace :: (Show a, Show s)
                    => String -> (a -> String) -> [(s, S.Set (Prop a))] -> String
    showPrettyTrace summaryToken showap trace = show
      $ map (\(q, b) -> (q, if S.null b
                            then [summaryToken]
                            else map (showp showap) $ S.toList b)) trace


preprocess :: String -> T.Text -> IO T.Text
preprocess fname content = do
  processed <- mapM (include fname) (T.lines content)
  return $ T.unlines processed

include :: String -> T.Text -> IO T.Text
include fname line =
  case parse (spaceP *> includeP) fname line of
    Left  _    -> return line
    Right path -> readFile (takeDirectory fname </> path)


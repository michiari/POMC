{-# LANGUAGE DeriveDataTypeable #-}
{-# OPTIONS_GHC -fno-cse #-}
{- |
   Module      : Main
   Copyright   : 2020-2025 Davide Bergamaschi, Michele Chiari
   License     : MIT
   Maintainer  : Michele Chiari
-}

module Main (main) where

import Pomc.Check (fastcheckGen)
import Pomc.ModelChecker (modelCheckExplicitGen, modelCheckProgram, countStates)
import qualified Pomc.Z3Encoding as Z3 ( SMTOpts(..), defaultSmtOpts
                                       , modelCheckProgram, SMTResult(..), SMTStatus(..)
                                       )
import Pomc.Prob.ProbModelChecker (programTermination, qualitativeModelCheckProgram, quantitativeModelCheckProgram, exportMarkovChain)
import Pomc.Prob.ProbUtils (Solver(..), Stats(..))
import Pomc.Parse.Parser (checkRequestP, spaceP, CheckRequest(..), preprocess)
import Pomc.Prec (Prec(..))
import Pomc.Prop (Prop(..))
import Pomc.TimeUtils (timeAction, timeFunApp, timeToString)
import Pomc.LogUtils (LogLevel(..), selectLogVerbosity)

import Prelude hiding (readFile)
import Numeric (showEFloat)

import System.Exit
import System.FilePath
import System.Console.CmdArgs hiding (explicit)

import Text.Megaparsec
import Data.Text.IO (readFile)
import qualified Data.Text as T
import Data.Maybe (fromJust)
import Data.Word (Word64)

import Data.List (intersperse)

import qualified Data.Set as S

import Control.Monad

data PomcArgs = PomcArgs
  { finite :: Bool
  , infinite :: Bool
  , explicit :: Bool
  , smt      :: Word64
  , smt_use_array_theory :: Bool
  , noovi :: Bool
  , newton :: Bool
  , maxDepth :: Int
  , verbose :: Int
  , fileName :: FilePath
  } deriving (Data,Typeable,Show,Eq)

pomcArgs :: PomcArgs
pomcArgs = PomcArgs
  { finite = False &= help "Use finite-word semantics"
  , infinite = False &= help "Use infinite-word (omega) semantics (default)"
  , explicit = False &= help "Use the explicit-state model checking engine (default)"
  , smt = 0 &= help "Use the SMT-based model checking engine, specifying the maximum trace length"
  , smt_use_array_theory = False &= help "Encode arrays using the SMT theory of arrays (generally slower) instead of uninterpreted functions. Defaults to false."
  , noovi = False &= help "Use z3 instead of Optimistic Value Iteration for probabilistic model checking"
  , newton = False &= help "Use the Newton method to iterate fixpoint equations for probabilistic model checking"
  , maxDepth = 100 &= help "Max stack depth when exporting a Markov Chain representation of the input program with unfolded stack (default = 100)"
  , verbose = 0 &= help "Print more info about model checking progress. 0 = no logging (default), 1 = show info, 2 = debug mode"
  , fileName = def &= args &= typFile -- &= help "Input file"
  }
  &= summary "POMC v2.9.0"
  &= details [ "Only one input file can be specified."
             , "--finite and --infinite cannot be specified together."
             , "--explicit and --smt cannot be specified together."
             ]

main :: IO ()
main = do
  pargs <- cmdArgs pomcArgs
  when (infinite pargs && finite pargs)
    $ die "--finite and --infinite cannot be specified together."
  when (explicit pargs && smt pargs > 0)
    $ die "--explicit and --smt cannot be specified together."
  let isOmega = not $ finite pargs
      isExplicit = smt pargs == 0
      probSolver | noovi pargs = SMTWithHints
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
    ExplCheckRequest phis rawPrecRels maybeStrings maybeOpa
      | isExplicit -> do
          let precRels = addEndPrec rawPrecRels
          stringTimes <- case maybeStrings of
            Just strings -> forM [(phi, s) | phi <- phis, s <- strings]
                            (uncurry $ runString precRels)
            Nothing -> return []

          mcTimes <- case maybeOpa of
            Just opa -> forM phis (runMC isOmega opa)
            Nothing -> return []

          return $ sum stringTimes + sum mcTimes
      | otherwise -> putStrLn "String and OPA checking not supported in SMT mode."
                     >> return 0

    ProgCheckRequest phis prog -> sum <$> forM phis
      (runProg isOmega isExplicit logLevel (smt pargs) (smt_use_array_theory pargs) prog)

    ProbTermRequest _ prog -> runProbTerm logLevel probSolver prog
    ProbCheckRequest phi prog False -> runQualProbCheck logLevel probSolver phi prog
    ProbCheckRequest phi prog True -> runQuantProbCheck logLevel probSolver phi prog
    ProbUnfoldRequest phi prog -> runUnfoldAndExport logLevel phi prog depth fname

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

    runProg isOmega True _ _ _ prog phi = do
      putStr (concat [ "\nModel Checking\nFormula: ", show phi
                     , "\nResult:  "
                     ])
      ((sat, trace), time) <- timeFunApp fst (modelCheckProgram isOmega phi) prog
      putStr $ show sat
      unless (sat || isOmega) $ putStr $ "\nCounterexample: " ++ showPrettyTrace "..." show trace
      putStrLn (concat ["\nElapsed time: ", timeToString time])
      return time
    runProg False False isVerbose maxDepth smtUseArrayTheory prog phi = do
      putStrLn $ "\nSMT-based Model Checking\nFormula: " ++ show phi
      smtres <- Z3.modelCheckProgram ((Z3.defaultSmtOpts maxDepth) { Z3.smtVerbose = isVerbose
                                                                   , Z3.smtUseArrayTheory = smtUseArrayTheory
                                                                   })
                phi prog
      putStr $ "Result:  " ++ show (Z3.smtStatus smtres)
      when (Z3.smtStatus smtres == Z3.Unsat)
        $ putStr $ "\nCounterexample: " ++ show (fromJust $ Z3.smtTableau smtres)
      let time = Z3.smtTimeAssert smtres + Z3.smtTimeCheck smtres + Z3.smtTimeModel smtres
      putStrLn $ concat [ "\nElapsed time: ", timeToString time
                        , " (encoding: ",     timeToString (Z3.smtTimeAssert smtres)
                        , ", solver: ",       timeToString (Z3.smtTimeCheck smtres)
                        , ", model: ",        timeToString (Z3.smtTimeModel smtres)
                        , ")"
                        ]
      return time
    runProg True False _ _ _ _ _ =
      error "Infinite-word model checking not yet supported in SMT mode."

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
      putStr ("\nFloating Point Result:  " ++ show (fromRational lb, fromRational ub))
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

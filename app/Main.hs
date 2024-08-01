{-# LANGUAGE DeriveDataTypeable #-}
{-# OPTIONS_GHC -fno-cse #-}
{- |
   Module      : Main
   Copyright   : 2020-2024 Davide Bergamaschi, Michele Chiari
   License     : MIT
   Maintainer  : Michele Chiari
-}

module Main (main) where

import Pomc.Check (fastcheckGen)
import Pomc.ModelChecker (modelCheckExplicitGen, modelCheckProgram, countStates)
import qualified Pomc.Z3Encoding as Z3 ( SMTOpts(..), defaultSmtOpts
                                       , modelCheckProgram, SMTResult(..), SMTStatus(..)
                                       )
import Pomc.Parse.Parser (checkRequestP, spaceP, CheckRequest(..), includeP)
import Pomc.Prec (Prec(..))
import Pomc.Prop (Prop(..))
import Pomc.TimeUtils (timeFunApp, timeToString)
import Pomc.LogUtils (LogLevel(..))

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
  { finite   :: Bool
  , infinite :: Bool
  , explicit :: Bool
  , smt      :: Word64
  , smt_use_array_theory :: Bool
  , fileName :: FilePath
  , verbose  :: Bool
  } deriving (Data, Typeable, Show, Eq)

pomcArgs :: PomcArgs
pomcArgs = PomcArgs
  { finite = False &= help "Use finite-word semantics"
  , infinite = False &= help "Use infinite-word (omega) semantics (default)"
  , explicit = False &= help "Use the explicit-state model checking engine (default)"
  , smt = 0 &= help "Use the SMT-based model checking engine, specifying the maximum trace length"
  , smt_use_array_theory = False &= help "Encode arrays using the SMT theory of arrays (generally slower) instead of uninterpreted functions. Defaults to false."
  , fileName = def &= args &= typFile -- &= help "Input file"
  , verbose = False &= help "Print more info about model checking progress (currently only works with --smt)"
  }
  &= summary "POMC v2.1.0"
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
      fname = fileName pargs

  fcontent <- readFile fname
  prepcontent <- preprocess fname fcontent

  creq <- case parse (spaceP *> checkRequestP <* eof) fname prepcontent of
            Left  errBundle -> die (errorBundlePretty errBundle)
            Right creq      -> return creq
  totalTime <- case creq of
    ExplCheckRequest phis rawPrecRels maybeStrings maybeOpa
      | isExplicit -> putStrLn "String and OPA checking not supported in SMT mode."
                      >> return 0
      | otherwise -> do
          let precRels = addEndPrec rawPrecRels
          stringTimes <- case maybeStrings of
            Just strings -> forM [(phi, s) | phi <- phis, s <- strings]
                            (uncurry $ runString precRels)
            Nothing -> return []

          mcTimes <- case maybeOpa of
            Just opa -> forM phis (runMC isOmega opa)
            Nothing -> return []

          return $ sum stringTimes + sum mcTimes

    ProgCheckRequest phis prog -> sum <$> forM phis
      (runProg isOmega isExplicit logVerbosity (smt pargs) (smt_use_array_theory pargs) prog)
      where logVerbosity | verbose pargs = Just LevelInfo
                         | otherwise = Nothing

  putStrLn ("\n\nTotal elapsed time: " ++ timeToString totalTime ++
            " (" ++ showEFloat (Just 4) totalTime " s)")
  where
    runString precRels phi s = do
      putStr (concat [ "\nFormula: ", show phi
                     , "\nString:  ", showstring s
                     , "\nResult:  "
                     ])
      (sat, time) <- timeFunApp id (fastcheckGen phi precRels) s
      print sat
      putStrLn (concat ["\nElapsed time: ", timeToString time])
      return time

    runMC isOmega opa phi = do
      putStr (concat [ "\nModel Checking\nFormula: ", show phi
                     , "\nInput OPA state count: ", show $ countStates opa
                     , "\nResult:  "
                     ])
      ((sat, trace), time) <- timeFunApp fst (modelCheckExplicitGen isOmega phi) opa
      print sat
      unless sat $ putStr $ "\nCounterexample: " ++ showPrettyTrace "..." T.unpack trace
      putStrLn (concat ["\nElapsed time: ", timeToString time])
      return time

    runProg isOmega True _ _ _ prog phi = do
      putStr (concat [ "\nModel Checking\nFormula: ", show phi
                     , "\nResult:  "
                     ])
      ((sat, trace), time) <- timeFunApp fst (modelCheckProgram isOmega phi) prog
      print sat
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
preprocess fname content = fmap T.unlines $ mapM (include fname) (T.lines content)

include :: String -> T.Text -> IO T.Text
include fname line =
  case parse (spaceP *> includeP) fname line of
    Left  _    -> return line
    Right path -> readFile (takeDirectory fname </> path)

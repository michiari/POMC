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
import qualified Pomc.Z3Encoding as Z3 (modelCheckProgram, SMTResult(..), SMTStatus(..))
import Pomc.Parse (checkRequestP, spaceP, CheckRequest(..), includeP)
import Pomc.Prec (Prec(..))
import Pomc.Prop (Prop(..))
import Pomc.Util (timeAction, timeToString, prettyTrace)

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
  , fileName :: FilePath
  } deriving (Data, Typeable, Show, Eq)

pomcArgs :: PomcArgs
pomcArgs = PomcArgs
  { finite = False &= help "Use finite-word semantics"
  , infinite = False &= help "Use infinite-word (omega) semantics (default)"
  , explicit = False &= help "Use the explicit-state model checking engine (default)"
  , smt = 0 &= help "Use the SMT-based model checking engine, specifying the maximum trace length"
  , fileName = def &= args &= typFile -- &= help "Input file"
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

  let phis = creqFormulas creq
      precRels = addEndPrec . fromJust . creqPrecRels $ creq

  stringTimes <- case creqStrings creq of
    Just strings | isExplicit -> forM [(phi, s) | phi <- phis, s <- strings]
                                 (uncurry $ runString precRels)
                 | otherwise -> putStrLn "String checking not supported in SMT mode."
                                >> return []
    Nothing -> return []

  mcTimes <- case creqOpa creq of
    Just opa | isExplicit -> forM phis (runMC isOmega opa)
             | otherwise -> putStrLn "OPA checking not supported in SMT mode."
                            >> return []
    Nothing -> return []

  progTime <- case creqMiniProc creq of
    Just prog -> forM phis (runProg isOmega isExplicit (smt pargs) prog)
    Nothing -> return []

  let totalTime = sum stringTimes + sum mcTimes + sum progTime
  putStrLn ("\n\nTotal elapsed time: " ++ timeToString totalTime ++
            " (" ++ showEFloat (Just 4) totalTime " s)")

  where runString precRels phi s = do
          putStr (concat [ "\nFormula: ", show phi
                         , "\nString:  ", showstring s
                         , "\nResult:  "
                         ])
          (_, time) <- timeAction . putStr . show $ fastcheckGen phi precRels s
          putStrLn (concat ["\nElapsed time: ", timeToString time])
          return time

        runMC isOmega opa phi = do
          putStr (concat [ "\nModel Checking\nFormula: ", show phi
                         , "\nInput OPA state count: ", show $ countStates opa
                         , "\nResult:  "
                         ])
          ((sat, trace), time) <- timeAction $ do
            let st@(s, _) = modelCheckExplicitGen isOmega phi opa
            putStr $ show s
            return st
          unless sat $ putStr $ "\nCounterexample: "
            ++ (show . prettyTrace (T.singleton '#') (T.pack "...") $ trace)
          putStrLn (concat ["\nElapsed time: ", timeToString time])
          return time

        runProg isOmega True _ prog phi = do
          putStr (concat [ "\nExplicit-state Model Checking\nFormula: ", show phi
                         , "\nResult:  "
                         ])
          ((sat, trace), time) <- timeAction $ do
            let st@(s, _) = modelCheckProgram isOmega phi prog
            putStr $ show s
            return st
          unless (sat || isOmega) $ putStr $ "\nCounterexample: "
            ++ (show . prettyTrace (T.singleton '#') (T.pack "...") $ trace)
          putStrLn (concat ["\nElapsed time: ", timeToString time])
          return time
        runProg False False maxDepth prog phi = do
          putStr (concat [ "\nSMT-based Model Checking\nFormula: ", show phi
                         , "\nResult:  "
                         ])
          smtres <- Z3.modelCheckProgram (fmap T.unpack phi) prog maxDepth
          putStr $ show $ Z3.smtStatus smtres
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
        runProg True False _ _ _ =
          error "Infinite-word model checking not yet supported in SMT mode."

        addEndPrec precRels = noEndPR
                              ++ map (\p -> (End, p, Yield)) sl
                              ++ map (\p -> (p, End, Take)) sl
          where sl = S.toList $ S.fromList $ concatMap (\(sl1, sl2, _) -> [sl1, sl2]) noEndPR
                noEndPR = filter (\(p1, p2, _) -> p1 /= End && p2 /= End) precRels

        showp prop = case prop of Prop p -> show p
                                  End    -> "#"
        showpset pset = let showpset' = concat . intersperse " " . map showp . S.toList
                        in concat ["(", showpset' pset, ")"]
        showstring = concat . intersperse " " . map showpset


preprocess :: String -> T.Text -> IO T.Text
preprocess fname content = fmap T.unlines $ mapM (include fname) (T.lines content)

include :: String -> T.Text -> IO T.Text
include fname line =
  case parse (spaceP *> includeP) fname line of
    Left  _    -> return line
    Right path -> readFile (takeDirectory fname </> path)

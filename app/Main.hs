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
import Pomc.Parse.Parser (checkRequestP, spaceP, CheckRequest(..), includeP)
import Pomc.Prec (Prec(..))
import Pomc.Prop (Prop(..))
import Pomc.Util (timeAction, timeToString)

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
  , fileName :: FilePath
  } deriving (Data,Typeable,Show,Eq)

pomcArgs :: PomcArgs
pomcArgs = PomcArgs
  { finite = False &= help "Use finite-word semantics"
  , infinite = False &= help "Use infinite-word (omega) semantics (default)"
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
      fname = fileName pargs

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

  putStrLn ("\n\nTotal elapsed time: " ++ timeToString totalTime ++
            " (" ++ showEFloat (Just 4) totalTime " s)")
  where
    runString precRels phi s = do
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
        let (s, t) = modelCheckExplicitGen isOmega phi opa
        putStr $ show s
        return (s, t)
      unless sat $ putStr $ "\nCounterexample: " ++ showPrettyTrace "..." T.unpack trace
      putStrLn (concat ["\nElapsed time: ", timeToString time])
      return time

    runProg isOmega prog phi = do
      putStr (concat [ "\nModel Checking\nFormula: ", show phi
                     , "\nResult:  "
                     ])
      ((sat, trace), time) <- timeAction $ do
        let (s, t) = modelCheckProgram isOmega phi prog
        putStr $ show s
        return (s, t)
      unless sat $ putStr $ "\nCounterexample: " ++ showPrettyTrace "..." show trace
      putStrLn (concat ["\nElapsed time: ", timeToString time])
      return time

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


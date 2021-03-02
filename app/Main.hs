{- |
   Module      : Main
   Copyright   : 2021 Davide Bergamaschi, Michele Chiari
   License     : MIT
   Maintainer  : Michele Chiari
-}

module Main (main) where

import Pomc.Check (fastcheckGen)
import Pomc.ModelChecker (modelCheckGen, countStates)
import Pomc.Parse (checkRequestP, spaceP, CheckRequest(..), includeP)
import Pomc.MiniProc (programToOpa)
import Pomc.Prec (Prec(..))
import Pomc.Prop (Prop(..))
import Pomc.Util (safeHead, timeAction, timeToString)

import Prelude hiding (readFile)
import Numeric (showEFloat)

import System.Environment
import System.Exit
import System.FilePath

import Text.Megaparsec
import Data.Text.IO (readFile)
import qualified Data.Text as T
import Data.Maybe (fromJust)

import Data.List (intersperse)

import qualified Data.Set as S

import Control.Monad

main :: IO ()
main = do
  args <- getArgs
  fname <- case safeHead args of
             (Just "--help") -> exitHelp
             (Just fname)    -> return fname
             Nothing         -> exitHelp
  fcontent <- readFile fname
  prepcontent <- preprocess fname fcontent

  creq <- case parse (spaceP *> checkRequestP <* eof) fname prepcontent of
            Left  errBundle -> die (errorBundlePretty errBundle)
            Right creq      -> return creq

  let phis = creqFormulas creq
      precRels = addEndPrec . fromJust . creqPrecRels $ creq

  stringTimes <- case creqStrings creq of
                   Just strings -> forM [(phi, s) | phi <- phis, s <- strings]
                                   (uncurry $ runString precRels)
                   Nothing -> return []

  mcTimes <- case creqOpa creq of
               Just opa -> forM phis (runMC opa)
               Nothing -> return []

  progTime <- case creqMiniProc creq of
                Just prog -> forM phis (runProg prog)
                Nothing -> return []

  let totalTime = sum stringTimes + sum mcTimes + sum progTime
  putStrLn ("\n\nTotal elapsed time: " ++ timeToString totalTime ++
            " (" ++ showEFloat (Just 4) totalTime " s)")

  where runString precRels phi s =
          do putStr (concat [ "\nFormula: ", show phi
                            , "\nString:  ", showstring s
                            , "\nResult:  "
                            ])
             (_, time) <- timeAction . putStr . show $ fastcheckGen phi precRels s
             putStrLn (concat ["\nElapsed time: ", timeToString time])
             return time

        runMC opa phi =
          do putStr (concat [ "\nModel Checking\nFormula: ", show phi
                            , "\nInput OPA state count: ", show $ countStates opa
                            , "\nResult:  "
                            ])
             ((sat, trace), time) <- timeAction $ do let (s, t) = modelCheckGen phi opa
                                                     putStr $ show s
                                                     return (s, t)
             if sat
               then return ()
               else putStr $ "\nCounterexample: " ++ show trace
             putStrLn (concat ["\nElapsed time: ", timeToString time])
             return time

        runProg prog phi = runMC (programToOpa prog) phi

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


exitHelp :: IO a
exitHelp = do progName <- getProgName
              die ("USAGE:    " ++ progName ++ " FILE")


preprocess :: String -> T.Text -> IO T.Text
preprocess fname content = do
  processed <- mapM (include fname) (T.lines content)
  return $ T.unlines processed

include :: String -> T.Text -> IO T.Text
include fname line =
  case parse (spaceP *> includeP) fname line of
    Left  _    -> return line
    Right path -> readFile (takeDirectory fname </> path)


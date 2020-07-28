{- |
   Module      : Pomc.App
   Copyright   : 2020 Davide Bergamaschi, Michele Chiari
   License     : MIT
   Maintainer  : Michele Chiari
-}

module Pomc.App (go) where

import Pomc.Check (Checkable(..), fastcheckGen)
import Pomc.Parse (checkRequestP, spaceP, CheckRequest(..))
import Pomc.Prec (fromRelations)
import Pomc.Prop (Prop(..))
import Pomc.RPotl (getProps)
import Pomc.Util (safeHead, timeAction, timeToString)
import Pomc.PropConv (APType)

import Prelude hiding (readFile)

import System.Environment
import System.Exit

import Text.Megaparsec
import Data.Text.IO (readFile)

import Data.List (intersperse)

import Data.Set (Set)
import qualified Data.Set as S

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M

import Data.Maybe (fromJust)

import Control.Monad

import Data.Text (Text)

go :: IO ()
go = do args <- getArgs
        fname <- case safeHead args of
                   (Just "--help") -> exitHelp
                   (Just fname)    -> return fname
                   Nothing         -> exitHelp
        fcontent <- readFile fname

        creq <- case parse (spaceP *> checkRequestP <* eof) fname fcontent of
                  Left  errBundle -> die (errorBundlePretty errBundle)
                  Right creq      -> return creq

        let phis = creqFormulas creq
            strings = creqStrings creq
            precRels = creqPrecRels creq

        times <- forM [(phi, s) | phi <- phis, s <- strings] (uncurry $ run precRels)

        putStrLn ("\n\nTotal elapsed time: " ++ timeToString (sum times))
  where run precRels phi s =
          do putStr (concat [ "\nFormula: ", show phi
                            , "\nString:  ", showstring s
                            , "\nResult:  "
                            ])

             (_, time) <- timeAction . putStr . show $ fastcheckGen phi precRels s

             putStrLn (concat ["\nElapsed time: ", timeToString time])

             return time

        showp prop = case prop of Prop p -> show p
                                  End    -> "#"
        showpset pset = let showpset' = concat . intersperse " " . map showp . S.toList
                        in concat ["(", showpset' pset, ")"]
        showstring = concat . intersperse " " . map showpset


exitHelp :: IO a
exitHelp = do progName <- getProgName
              die ("USAGE:    " ++ progName ++ " FILE")

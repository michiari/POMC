import POMC.RPotl (Prop(..))
import POMC.Check (fastcheck)
import POMC.Example (stlPrecedenceV2)
import POMC.Parse (checkRequestP, spaceP, CheckRequest(..)) 
import POMC.Prec (makePrecFunc)
import POMC.Util (safeHead)

import Prelude hiding (readFile)

import System.Environment
import System.Exit

import Text.Megaparsec
import Data.Text.IO (readFile)

import qualified Data.Set as S

import Data.List (intersperse)

import Control.Monad

exitHelp :: IO a
exitHelp = do progName <- getProgName
              die ("USAGE:    " ++ progName ++ " FILE")

main :: IO ()
main = do args <- getArgs
          fname <- case safeHead args of
                     (Just "--help") -> exitHelp
                     (Just fname)    -> return fname
                     Nothing         -> exitHelp
          fcontent <- readFile fname
          checkReq <- case parse (spaceP *> checkRequestP <* eof) fname fcontent of
                        Left  errBundle -> die (errorBundlePretty errBundle)
                        Right checkReq  -> return checkReq
          let pf = makePrecFunc (creqPrecRules checkReq)
          forM [(f, s, fastcheck f pf s) | f <- creqFormulas checkReq, s <- creqStrings checkReq]
               (putStrLn . showResult)
          return ()
  where showResult (f, s, r) = concat [ "\nFormula: ", show f
                                      , "\nString:  ", showstring s
                                      , "\nResult:  ", show r 
                                      ]
        showp prop = case prop of Prop p -> show p
                                  End    -> "#"
        showpset pset = let showpset' = concat . intersperse " " . map showp . S.toList 
                        in concat ["(", showpset' pset, ")"]
        showstring = concat . intersperse " " . map showpset

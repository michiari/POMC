import POMC.Check (fastcheck)
import POMC.Parse (checkRequestP, spaceP, CheckRequest(..))
import POMC.Prec (fromRelations)
import POMC.Prop (Prop(..))
import POMC.Util (safeHead, timeAction)

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
          let pf = fromRelations (creqPrecRels checkReq)
          forM_ [(f, s) | f <- creqFormulas checkReq, s <- creqStrings checkReq] (runreq pf)
  where runreq pf (f, s) = do putStr (concat [ "\nFormula: ", show f
                                             , "\nString:  ", showstring s
                                             , "\nResult:  "
                                             ])
                              (_, secs, _) <- timeAction . putStr . show $ fastcheck f pf s
                              putStrLn (concat ["\nElapsed: ", secs])
        showp prop = case prop of Prop p -> show p
                                  End    -> "#"
        showpset pset = let showpset' = concat . intersperse " " . map showp . S.toList
                        in concat ["(", showpset' pset, ")"]
        showstring = concat . intersperse " " . map showpset

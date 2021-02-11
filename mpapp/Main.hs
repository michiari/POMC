import Prelude hiding (readFile)

import Pomc.MiniProcParse (programP)
import Pomc.MiniProc (programToOpa)
import Pomc.Util (safeHead)

import Text.Megaparsec
import System.Environment
import System.Exit
import Data.Text.IO (readFile)

main :: IO ()
main = do args <- getArgs
          fileName <- case safeHead args of
                        Just fname -> return fname
                        Nothing    -> die "No input."
          fileCont <- readFile fileName
          prog <- case parse programP fileName fileCont of
                  Left  errBundle -> die (errorBundlePretty errBundle)
                  Right fsks      -> return fsks
          putStrLn . show $ prog
          putStrLn . show . programToOpa $ prog

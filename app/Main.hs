import POMC.Check (Checkable(..), closure, fastcheck)
import POMC.Parse (checkRequestP, spaceP, CheckRequest(..))
import POMC.Prec (fromRelations)
import POMC.Prop (Prop(..))
import POMC.RPotl (Formula(..))
import POMC.Util (safeHead, timeAction, timeToString)

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

          creq <- case parse (spaceP *> checkRequestP <* eof) fname fcontent of
                    Left  errBundle -> die (errorBundlePretty errBundle)
                    Right creq      -> return creq

          let tfunc = makeTransFunc creq

              pfunc = fromRelations (transPrecRels tfunc . creqPrecRels $ creq)

              phis = creqFormulas creq
              strings = creqStrings creq

          times <- forM [(phi, s) | phi <- phis, s <- strings] (uncurry $ run tfunc pfunc)

          putStrLn ("\n\nTotal elapsed time: " ++ timeToString (sum times))
  where run tfunc pfunc phi s =
          do putStr (concat [ "\nFormula: ", show phi
                            , "\nString:  ", showstring s
                            , "\nResult:  "
                            ])

             let tphi = transFormula tfunc phi
                 ts   = transString  tfunc s

             (_, time) <- timeAction . putStr . show $ fastcheck tphi pfunc ts

             putStrLn (concat ["\nElapsed time: ", timeToString time])

             return time

        showp prop = case prop of Prop p -> show p
                                  End    -> "#"
        showpset pset = let showpset' = concat . intersperse " " . map showp . S.toList
                        in concat ["(", showpset' pset, ")"]
        showstring = concat . intersperse " " . map showpset

        transPrecRels tfunc rels = map (\(s1, s2, pr) -> ( S.map (fmap tfunc) s1
                                                         , S.map (fmap tfunc) s2
                                                         , pr
                                                         )
                                       ) rels
        transFormula tfunc phi = tfunc <$> phi
        transString tfunc string = S.map (fmap tfunc) <$> string

makeTransFunc :: CheckRequest -> (Text -> Int)
makeTransFunc (CheckRequest rels phis strings) =
  let relProps = (concatMap (\(s1, s2, _) -> S.toList $ S.union s1 s2) rels)

      phiProps = concatMap (\phi -> let rphi = toReducedPotl phi
                                 in [p | Atomic p <- S.toList (closure rphi [])]
                           ) phis

      stringProps = concatMap (\s -> concatMap S.toList s) strings

      propSet :: Set (Prop Text)
      propSet = S.fromList (relProps ++ phiProps ++ stringProps)

      tmap :: Map Text Int
      tmap = M.fromList $ zip ([p | Prop p <- S.toList propSet]) [1..]

      trans :: Text -> Int
      trans t = fromJust $ M.lookup t tmap
  in trans

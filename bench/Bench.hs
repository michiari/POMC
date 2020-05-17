import POMC.Check (check, fastcheck)
import POMC.Example (stlPrecedence1, stlAnnotate1)
import POMC.Opa (Prec(..))
import POMC.RPotl (Formula(..), Prop(..), formulaAt)

import Control.Monad (forM_)

import Criterion.Measurement
import Criterion.Measurement.Types (nfIO, measTime)

import qualified Data.Set as S

import System.IO

-- Each bench case is a tuple of the type:
-- (name, expected check result, phi, prec, input)
benchCases =
  [ ( "StlV1, PrecNext bench 1"
    , True
    , formulaAt 2 $ PrecNext (S.fromList [Yield]) (Atomic . Prop  $ "c_b")
    , stlPrecedence1
    , map (S.singleton . Prop) ["c_a", "han", "c_b", "c_c", "c_d", "t_a", "t_b", "t_c", "r_a"]
    )
  , ( "StlV1, PrecNext bench 2"
    , False
    , formulaAt 2 $ PrecNext (S.fromList [Equal, Take]) (Atomic . Prop  $ "c_b")
    , stlPrecedence1
    , map (S.singleton . Prop) ["c_a", "han", "c_b", "c_c", "c_d", "t_a", "t_b", "t_c", "r_a"]
    )
  , ( "StlV1, ChainNext bench 1"
    , True
    , formulaAt 2 $ ChainNext (S.fromList [Take]) (Atomic . Prop  $ "r_a")
    , stlPrecedence1
    , map (S.singleton . Prop) ["c_a", "han", "c_b", "c_c", "c_d", "t_a", "t_b", "t_c", "r_a"]
    )
  , ( "StlV1, ChainNext bench 2"
    , True
    , formulaAt 2 $ ChainNext (S.fromList [Yield]) (Atomic . Prop  $ "t_a")
    , stlPrecedence1
    , map (S.singleton . Prop) ["c_a", "han", "c_b", "c_c", "c_d", "t_a", "t_b", "t_c", "r_a"]
    )
  , ( "StlV1, Until bench 1"
    , True
    , formulaAt 3 $ Until (S.fromList [Equal, Take]) T (Atomic . Prop  $ "thr")
    , stlPrecedence1
    , map (S.singleton . Prop) ["call", "han", "call", "call", "call", "thr", "thr", "thr", "ret"]
    )
  , ( "StlV1, Until bench 2"
    , False
    , formulaAt 2 $ Until (S.fromList [Equal, Take]) T (Atomic . Prop  $ "thr")
    , stlPrecedence1
    , map (S.singleton . Prop) ["call", "han", "call", "call", "call", "thr", "thr", "thr", "ret"]
    )
  , ( "StlV1, Until bench 3"
    , True
    , Until (S.fromList [Yield, Equal]) T (Atomic . Prop  $ "thr")
    , stlPrecedence1
    , map (S.singleton . Prop) ["call", "han", "call", "call", "call", "thr", "thr", "thr", "ret"]
    )
  , ( "StlV1, HierNextYield bench 1"
    , True
    , formulaAt 6 $ HierNextYield (Atomic . Prop  $ "t_b")
    , stlPrecedence1
    , map (S.singleton . Prop) ["c_a", "han", "c_b", "c_c", "c_d", "t_a", "t_b", "t_c", "r_a"]
    )
  , ( "StlV1, HierBackYield bench 1"
    , True
    , formulaAt 7 $ HierBackYield (Atomic . Prop  $ "t_a")
    , stlPrecedence1
    , map (S.singleton . Prop) ["c_a", "han", "c_b", "c_c", "c_d", "t_a", "t_b", "t_c", "r_a"]
    )
  , ( "StlV1, ChainNext bench 3"
    , True
    , formulaAt 3 $ ChainNext (S.fromList [Take]) (Atomic . Prop  $ "thr")
    , stlPrecedence1
    , map (S.singleton . Prop) ["call", "han", "call", "call", "call", "thr", "thr", "thr", "ret"]
    )
  , ( "StlV1, ChainBack bench 1" -- ERROR!
    , True
    , formulaAt 6 $ ChainBack (S.fromList [Take]) (Atomic . Prop  $ "call")
    , stlPrecedence1
    , map (S.singleton . Prop) ["call", "han", "call", "call", "call", "thr", "thr", "thr", "ret"]
    )
  , ( "StlV1, ChainNext bench 4"
    , True
    , formulaAt 1 $ ChainNext (S.fromList [Equal]) (Atomic . Prop  $ "ret")
    , stlPrecedence1
    , map (S.singleton . Prop) ["call", "han", "call", "call", "call", "thr", "thr", "thr", "ret"]
    )
  , ( "StlV1, HierNextTake bench 1"
    , True
    , formulaAt 3 $ HierNextTake (Atomic . Prop  $ "c_c")
    , stlPrecedence1
    , map (S.singleton . Prop) ["c_a", "han", "c_b", "c_c", "c_d", "t_a", "t_b", "t_c", "r_a"]
    )
  , ( "StlV1, HierBackTake bench 1"
    , True
    , formulaAt 4 $ HierBackTake (Atomic . Prop  $ "c_b")
    , stlPrecedence1
    , map (S.singleton . Prop) ["c_a", "han", "c_b", "c_c", "c_d", "t_a", "t_b", "t_c", "r_a"]
    )
  , ( "StlV1, Until bench 4"
    , True
    , formulaAt 2 $ Until (S.fromList [Yield]) ((Atomic . Prop  $ "han") `Or` (Atomic . Prop  $ "thr")) (Atomic . Prop  $ "t_b")
    , stlPrecedence1
    , map (S.fromList . map Prop) (stlAnnotate1 ["c_a", "han", "c_b", "c_c", "c_d", "t_a", "t_b", "t_c", "r_a"])
    )
  , ( "StlV1, Since bench 1"
    , True
    , formulaAt 7 $ Since (S.fromList [Take]) (Atomic . Prop  $ "thr") (Atomic . Prop  $ "c_c")
    , stlPrecedence1
    , map (S.fromList . map Prop) (stlAnnotate1 ["c_a", "han", "c_b", "c_c", "c_d", "t_a", "t_b", "t_c", "r_a"])
    )
  , ( "StlV1, HierUntilYield bench 1"
    , True
    , formulaAt 6 $ (Atomic . Prop  $ "thr") `HierUntilYield` (Atomic . Prop  $ "t_c")
    , stlPrecedence1
    , map (S.fromList . map Prop) (stlAnnotate1 ["c_a", "han", "c_b", "c_c", "c_d", "t_a", "t_b", "t_c", "r_a"])
    )
  , ( "StlV1, HierSinceYield bench 1"
    , True
    , formulaAt 8 $ (Atomic . Prop  $ "thr") `HierSinceYield` (Atomic . Prop  $ "t_a")
    , stlPrecedence1
    , map (S.fromList . map Prop) (stlAnnotate1 ["c_a", "han", "c_b", "c_c", "c_d", "t_a", "t_b", "t_c", "r_a"])
    )
  , ( "StlV1, HierUntilTake bench 1"
    , True
    , formulaAt 3 $ (Atomic . Prop  $ "call") `HierUntilTake` (Atomic . Prop  $ "c_c")
    , stlPrecedence1
    , map (S.fromList . map Prop) (stlAnnotate1 ["c_a", "han", "c_b", "c_c", "c_d", "t_a", "t_b", "t_c", "r_a"])
    )
  , ( "StlV1, HierSinceTake bench 1"
    , True
    , formulaAt 4 $ (Atomic . Prop  $ "call") `HierSinceTake` (Atomic . Prop  $ "c_b")
    , stlPrecedence1
    , map (S.fromList . map Prop) (stlAnnotate1 ["c_a", "han", "c_b", "c_c", "c_d", "t_a", "t_b", "t_c", "r_a"])
    )
  ]

benchCheck name expected phi prec ts =
  if expected == fastcheck phi prec ts
    then putStrLn (name ++ ": success")
    else putStrLn (name ++ ": failure")

runCase (name, expected, phi, prec, ts) = do
  (measured, _) <- measure (nfIO $ benchCheck name expected phi prec ts) 1
  putStrLn ("Elapsed: " ++ secs (measTime measured) ++ "\n")

main = do
  hSetBuffering stdout LineBuffering
  mapM_ runCase benchCases

{-# LANGUAGE DeriveGeneric, DeriveAnyClass #-}

{- |
   Module      : Pomc.Prob.ProbUtils.hs
   Copyright   : 2023 Francesco Pontiggia
   License     : MIT
   Maintainer  : Francesco Pontiggia
-}

module Pomc.Prob.ProbUtils ( Prob
                           , EqMapNumbersType
                           , Distr(..)
                           , RichDistr
                           , Label
                           , StateId(..)
                           , Stack
                           , DeltaWrapper(..)
                           , SIdGen
                           , Solver(..)
                           , Comp(..)
                           , TermQuery(..)
                           , TermResult(..)
                           , Stats(..)
                           , initSIdGen
                           , sIdCount
                           , sIdMap
                           , wrapState
                           , freshPosId
                           , freshNegId
                           , decode
                           , defaultTolerance
                           , defaultRTolerance
                           , encodeInitialSemiconf
                           , solver
                           , toBool
                           , toTermResult
                           , toLowerProb
                           , toUpperProb
                           , extractUpperProb
                           , extractUpperDouble
                           , extractLowerProb
                           , newStats
                           , debug
                           , showFlatModel
                           ) where
import Prelude hiding(appendFile)
import Pomc.State(Input, State)
import Pomc.Encoding (nat)
import Pomc.Check (EncPrecFunc)
import Pomc.Prec (Prec(..))

import qualified Pomc.Encoding as E
import qualified Pomc.Prob.ProbEncoding as PE

import qualified Control.Monad.ST as ST
import Data.STRef (STRef, newSTRef, readSTRef, modifySTRef')
import GHC.Generics (Generic)
import Control.DeepSeq (NFData)
import Pomc.LogUtils (MonadLogger, logDebugN, logInfoN)

import Data.Hashable
import qualified Data.HashTable.ST.Basic as BH
import qualified Data.HashTable.Class as H

import Data.Map(Map)

import qualified Data.Set as Set

import Data.Maybe (fromJust, isNothing, catMaybes)

import Control.Monad.ST (RealWorld)
import Data.STRef (newSTRef, readSTRef, modifySTRef')

import Control.Monad.IO.Class (MonadIO (liftIO))

import Data.Bifunctor(second)

import qualified Data.Strict.Map as StrictMap

import Data.Char (isLower, toLower)

import Data.Text.IO (appendFile)
import qualified Data.Text as T

import Z3.Monad hiding (Solver)
import Control.Monad (when)
import Pomc.Z3T (liftSTtoIO)
import Pomc.PropConv (APType)
import Pomc.Potl (Formula(..), Prop (Prop, End))

type Prob = Rational
type EqMapNumbersType = Double
newtype Distr a = Distr [(a, Prob)] deriving Show
-- a distribution over elements of type a
-- with some additional labels of type b
type RichDistr a b = [(a, b, Prob)]

-- in probabilistic systems the input is replaced by state labels
type Label = Input

-- a basic open-addressing hashtable using linear probing
-- s = thread state, k = key, v = value.
type HashTable s k v = BH.HashTable s k v

-- States with unique IDs
data StateId state = StateId { getId :: !Int
                             , getState :: state
                             , getLabel :: Label
                             } deriving (Show)

instance Eq (StateId state) where
  p == q = getId p == getId q

instance Ord (StateId state) where
  compare p q = compare (getId p) (getId q)

instance Hashable (StateId state) where
  hashWithSalt salt s = hashWithSalt salt $ getId s

-- a type to keep track of state to id relation
data SIdGen s state = SIdGen
  { idSequence :: STRef s Int -- a mutable variable in state thread s containing a variable of type Int
  , stateToId :: HashTable s state (StateId state) -- an HashTable where (key,value) = (state, StateId)
  }

initSIdGen :: ST.ST s (SIdGen s state)
initSIdGen = do
  newIdSequence <- newSTRef (0 :: Int) -- build a integer new STRef in the current state thread
  newStateToId <- H.new -- new empty HashTable
  return $ SIdGen { idSequence = newIdSequence,
                    stateToId = newStateToId }

sIdCount :: SIdGen s state -> ST.ST s Int
sIdCount sig = readSTRef (idSequence sig)

sIdMap :: (Ord state) => SIdGen s state -> ST.ST s (StrictMap.Map state Int)
sIdMap sig = StrictMap.fromList . map (second getId) <$> H.toList (stateToId sig)

-- wrap a State into the StateId data type and into the ST monad, and update accordingly SidGen
wrapState :: (Eq state, Hashable state)
          => SIdGen s state
          -> state
          -> Label
          -> ST.ST s (StateId state)
wrapState sig q l = do
  qwrapped <- H.lookup (stateToId sig) q
  maybe (do
    let idSeq = idSequence sig
    newId <- readSTRef idSeq
    modifySTRef' idSeq (+1)
    let newQwrapped = StateId newId q l
    H.insert (stateToId sig) q newQwrapped
    return newQwrapped) return qwrapped

-- Stack symbol: (input token, state) || Bottom if empty stack
type Stack state = Maybe (Input, StateId state)

-- a type for the probabilistic delta relation of the popa and the delta relation of the phiAutomaton
data DeltaWrapper pState = Delta
  { bitenc :: E.BitEncoding
  , proBitenc :: PE.ProBitencoding
  , prec :: EncPrecFunc
  , deltaPush :: pState -> RichDistr pState Label
  , deltaShift :: pState -> RichDistr pState Label
  , deltaPop :: pState -> pState -> RichDistr pState Label
  , phiDeltaPush :: State -> [State]
  , phiDeltaShift :: State -> [State]
  , phiDeltaPop :: State -> State -> [State]
  }

freshPosId :: STRef s Int -> ST.ST s Int
freshPosId idSeq = do
  curr <- readSTRef idSeq
  modifySTRef' idSeq (+1);
  return curr

freshNegId :: STRef s Int -> ST.ST s Int
freshNegId idSeq = do
  curr <- readSTRef idSeq
  modifySTRef' idSeq (\i -> i - 1);
  return curr

decode :: (StateId state, Stack state) -> (Int,Int,Int)
decode (s1, Nothing) = (getId s1, 0, 0)
decode (s1, Just (i, s2)) = (getId s1, nat i, getId s2)

decodeFullStack :: (StateId state, [Stack state]) -> (Int,[(Int,Int)])
decodeFullStack (s1, s) = (getId s1, map dec s)
  where dec Nothing = (0,0)
        dec (Just (i, s2)) = (nat i, getId s2)

-- Strategy to use to compute the result
-- SMTWithHints: compute a lower approximation of the solution
--               with an iterative method and use it as a hint for the SMT solver
data Solver = SMTWithHints | ExactSMTWithHints | OVI deriving (Eq, Show)

defaultTolerance :: EqMapNumbersType
defaultTolerance = 1e-5

defaultRTolerance :: Prob
defaultRTolerance = 1e-5

-- different termination queries
-- CompQuery asks whether the probability to terminate is <, <=, >, >= than the given probability depending on Comp
-- ApproxQuery requires to approximate the termination probabilities of all semiconfs of the support graph
-- ApproxTermination requires to approximate just the overall termination probability of the given popa
data TermQuery = CompQuery Comp Prob Solver
               | ApproxAllQuery Solver
               | ApproxSingleQuery Solver
  deriving (Show, Eq)

data Comp = Lt | Le | Gt | Ge deriving (Show, Eq)

encodeInitialSemiconf :: TermQuery -> Bool
encodeInitialSemiconf (ApproxSingleQuery _) = True
encodeInitialSemiconf (CompQuery{}) = True
encodeInitialSemiconf _ = False

solver :: TermQuery -> Solver
solver (CompQuery _ _ s) = s
solver (ApproxAllQuery s) = s
solver (ApproxSingleQuery s) = s

-- different possible results of a termination query
-- ApproxAllResult represents the approximated probabilities to terminate of all the semiconfs of the popa 
-- ApproxSingleResult represents the approximate probability to terminate of the popa 
data TermResult = TermSat | TermUnsat | ApproxAllResult (Map (Int,Int) Prob, Map (Int,Int) Prob) | ApproxSingleResult (Prob, Prob)
  deriving (Show, Eq, Generic, NFData)

toBool :: TermResult -> Bool
toBool TermSat = True
toBool TermUnsat = False
toBool r = error $ "cannot convert a non boolean result. Got instead: " ++ show r

toTermResult :: Bool -> TermResult
toTermResult True = TermSat
toTermResult False = TermUnsat

toLowerProb :: TermResult -> Prob
toLowerProb (ApproxSingleResult (lb, _)) = lb
toLowerProb r = error $ "cannot convert a non single probability result. Got instead: " ++ show r

toUpperProb :: TermResult -> Prob
toUpperProb (ApproxSingleResult (_, ub)) = ub
toUpperProb r = error $ "cannot convert a non single probability result. Got instead: " ++ show r

extractUpperAst :: (MonadLogger z3, MonadZ3 z3) => AST -> z3 AST
extractUpperAst ast = do
  isAlgebraic <- isAlgebraicNumber ast
  logDebugN . ("AST kind: " ++) . show =<< getAstKind ast
  logDebugN . ("Is it an algebraic number: " ++) . show =<< isAlgebraicNumber ast
  logDebugN . ("Is it a numeral number: " ++) . show =<< isNumeralAst ast
  logDebugN . ("AST string representation: " ++) . show =<< astToString ast
  if isAlgebraic
    then getAlgebraicNumberUpper ast 5
    else return ast

extractUpperProb :: (MonadLogger z3, MonadZ3 z3) => AST -> z3 Prob
extractUpperProb ast = extractUpperAst ast >>= getReal

extractUpperDouble :: (MonadLogger z3, MonadZ3 z3) => AST -> z3 Double
extractUpperDouble ast = extractUpperAst ast >>= getNumeralDouble

extractLowerAst :: (MonadLogger z3, MonadZ3 z3) => AST -> z3 AST
extractLowerAst ast = do
  isAlgebraic <- isAlgebraicNumber ast
  logDebugN . ("AST kind: " ++) . show =<< getAstKind ast
  logDebugN . ("Is it an algebraic number: " ++) . show =<< isAlgebraicNumber ast
  logDebugN . ("Is it a numeral number: " ++) . show =<< isNumeralAst ast
  logDebugN . ("AST string representation: " ++) . show =<< astToString ast
  if isAlgebraic
    then getAlgebraicNumberLower ast 5
    else return ast

extractLowerProb :: (MonadLogger z3, MonadZ3 z3) => AST -> z3 Prob
extractLowerProb ast = extractLowerAst ast >>= getReal

data Stats = Stats { upperBoundTime :: Double
                   , pastTime :: Double
                   , gGraphTime :: Double
                   , quantWeightTime :: Double
                   , quantSolTime :: Double
                   , suppGraphLen :: Int
                   , popaStatesCount :: Int
                   , equationsCount :: Int
                   , nonTrivialEquationsCount :: Int
                   , sccCount :: Int
                   , largestSCCSemiconfsCount :: Int
                   , largestSCCEqsCount :: Int
                   -- quantitative model checking OVI stats
                   , equationsCountQuant :: Int
                   , nonTrivialEquationsCountQuant :: Int
                   , sccCountQuant :: Int
                   , largestSCCSemiconfsCountQuant :: Int
                   , largestSCCNonTrivialEqsCountQuant :: Int
                   , gGraphSize :: Int
                   }

newStats :: Stats
newStats = Stats 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0

debug :: String -> a -> a
--debug = DBG.trace
debug _ x = x

-- generate a string representing a flattened version of a pOPA (a DTMC),
-- where the stack is unfolded into the model up to a parameter (depth) 
-- When stack's depth = max depth a state will just have a self loop.
-- We follow Storm syntax for explicit models,
-- and generate also a declaration of labels.

-- mutable variables
data Globals s state = Globals
  { sIdGen     :: SIdGen s state
  , idSeq      :: STRef s Int
  , graphMap   :: HashTable s (Int,[(Int,Int)]) Int
  }

showFlatModel :: (MonadIO m, MonadFail m, MonadLogger m, Ord state, Hashable state, Show state, Show a)
        => DeltaWrapper state -- probabilistic delta relation of a popa
        -> (state, Label) -- (initial state of the popa, label of the initial state)
        -> (APType -> a)
        -> Int -- maxDepth
        -> FilePath 
        -> FilePath
        -> m () -- returning a graph
showFlatModel probDelta (i,iLabel) decodeAP depth transFile labFile = do
  newSig <- liftSTtoIO $ initSIdGen
  initialsId <- liftSTtoIO $ wrapState newSig i iLabel
  let initialNode = (initialsId, [Nothing])
  newIdSequence <- liftSTtoIO $ newSTRef (0 :: Int)
  emptyGraphMap <- liftSTtoIO $ BH.new
  initialId <- liftSTtoIO $ freshPosId newIdSequence
  liftIO $ appendFile transFile (T.pack "dtmc")
  let labels = Set.toList . Set.filter skipEnd $ E.decode (bitenc probDelta) iLabel
      skipEnd (Atomic End) = False
      skipEnd (Not (Atomic End)) = False
      skipEnd _ = True
      showSymb = filter isLower . map toLower . show . decodeAP
      showAllFormulas (Atomic (Prop symb)) = showSymb symb
      showAllFormulas (Not (Atomic (Prop symb))) = showSymb symb
      showAllFormulas f = error $ "only props can be exported: " ++ show f
      checkDuplicates l = if length l /= length (Set.fromList l) then error ("trimmed labels overlap: " ++ show l) else l
  liftIO $ appendFile labFile $ T.pack $ concat ["#DECLARATION\ninit ", unwords (checkDuplicates . map showAllFormulas $ labels), "\n#END"]
  liftSTtoIO $ BH.insert emptyGraphMap (decodeFullStack initialNode) initialId
  let globals = Globals { sIdGen = newSig
                        , idSeq = newIdSequence
                        , graphMap = emptyGraphMap
                        }
  showUnfoldedStates [initialNode] globals probDelta decodeAP depth transFile labFile
  modelSize <- liftSTtoIO $ readSTRef (idSeq globals)
  logInfoN $ "Generated a model of size " ++ (show modelSize)

showUnfoldedStates :: (MonadIO m, MonadFail m, MonadLogger m, Eq state, Hashable state, Show state, Show a)
      => [(StateId state, [Stack state])] -- current state of the DTMC
      -> Globals RealWorld state -- global variables of the algorithm
      -> DeltaWrapper state -- delta relation of the popa
      -> (APType -> a)
      -> Int
      -> FilePath 
      -> FilePath
      -> m ()
showUnfoldedStates [] _ _ _ _ _ _ = return ()
showUnfoldedStates ((q,g):others) globals probDelta decodeAP depth transFile labFile =
  let qLabel = getLabel q
      qState = getState q
      precRel = (prec probDelta) (fst . fromJust . head $ g) qLabel
      labels = Set.toList . Set.filter skipEnd $ E.pdecode (bitenc probDelta) (getLabel q)
      skipEnd (Atomic End) = False
      skipEnd _ = True
      showSymb = filter isLower . map toLower . show . decodeAP
      showFormula (Atomic (Prop symb)) = showSymb symb
      showFormula _ = error "only props can be exported"
      cases

        | length g == depth && ((isNothing (head g)) || precRel == Just Yield) = do
          logInfoN "reached max stack depth - adding a self loop"
          _ <- showUnfoldedTransition globals (q,g) 1 (q,g) transFile
          return []

        -- this case includes the initial push
        | isNothing (head g) || precRel == Just Yield =
          showUnfoldedStatePush globals probDelta (q,g) qState qLabel transFile

        | precRel == Just Equal =
          showUnfoldedStateShift globals probDelta (q,g) qState qLabel transFile

        | precRel == Just Take =
          showUnfoldedStatePop globals probDelta (q,g) qState transFile

        | otherwise = return []

  -- adding labels
  in do 
  fromId <- liftSTtoIO $ fromJust <$>  BH.lookup (graphMap globals) (decodeFullStack (q,g))
  let maybeInit = if fromId == 0 then "init" : map showFormula labels else map showFormula labels
  liftIO $ appendFile labFile $ T.pack $ "\n" ++ unwords (show fromId : maybeInit)
  unencoded <- cases
  showUnfoldedStates (others ++ unencoded) globals probDelta decodeAP depth transFile labFile

showUnfoldedStatePush :: (MonadIO m, MonadFail m, MonadLogger m, Eq state, Hashable state, Show state)
      => Globals RealWorld state -- global variables of the algorithm
      -> DeltaWrapper state -- delta relation of the popa
      -> (StateId state, [Stack state]) -- current state of the DTMC
      -> state
      -> Label
      -> FilePath
      -> m [(StateId state, [Stack state]) ]
showUnfoldedStatePush globals probDelta (q,g) qState qLabel transFile =
  let showPush (p, pLabel, prob_) = do
        newState <- liftSTtoIO $ wrapState (sIdGen globals) p pLabel
        let newUnfoldedState = (newState, Just (qLabel, q) : g)
        showUnfoldedTransition globals (q,g) prob_ newUnfoldedState transFile
  in catMaybes <$> mapM showPush ((deltaPush probDelta) qState)

showUnfoldedStateShift :: (MonadIO m, MonadFail m, MonadLogger m, Eq state, Hashable state, Show state)
      => Globals RealWorld state -- global variables of the algorithm
      -> DeltaWrapper state -- delta relation of the popa
      -> (StateId state, [Stack state]) -- current state of the DTMC
      -> state
      -> Label
      -> FilePath
      -> m [(StateId state, [Stack state]) ]
showUnfoldedStateShift globals probDelta (q,g) qState qLabel transFile =
  let showShift (p, pLabel, prob_) = do
        newState <- liftSTtoIO $ wrapState (sIdGen globals) p pLabel
        let newUnfoldedState = (newState, Just (qLabel, snd . fromJust . head $ g): tail g)
        showUnfoldedTransition globals (q,g) prob_ newUnfoldedState transFile
  in catMaybes <$> mapM showShift ((deltaShift probDelta) qState)

showUnfoldedStatePop :: (MonadIO m, MonadFail m, MonadLogger m, Eq state, Hashable state, Show state)
      => Globals RealWorld state -- global variables of the algorithm
      -> DeltaWrapper state -- delta relation of the popa
      -> (StateId state, [Stack state]) -- current state of the DTMC
      -> state
      -> FilePath
      -> m [(StateId state, [Stack state]) ]
showUnfoldedStatePop globals probDelta (q,g) qState transFile =
  let showPop (p, pLabel, prob_) = do
        newState <- liftSTtoIO $ wrapState (sIdGen globals) p pLabel
        let newUnfoldedState = (newState, tail g)
        showUnfoldedTransition globals (q,g) prob_ newUnfoldedState transFile
  in catMaybes <$> mapM showPop ((deltaPop probDelta) qState (getState . snd . fromJust . head $ g))

showUnfoldedTransition :: (MonadIO m, MonadFail m, MonadLogger m, Eq state, Hashable state, Show state)
      => Globals RealWorld state -- global variables of the algorithm
      -> (StateId state, [Stack state]) -- current state of the DTMC
      -> Prob
      -> (StateId state, [Stack state]) -- destination state of the DTMC
      -> FilePath
      -> m (Maybe (StateId state, [Stack state])) -- do we need to encode dest?
showUnfoldedTransition globals from prob_ dest transFile = do 
    fromId <- liftSTtoIO $ fromJust <$> BH.lookup (graphMap globals) (decodeFullStack from)
    maybeId <- liftSTtoIO $ BH.lookup (graphMap globals) (decodeFullStack dest)
    actualId <- liftSTtoIO $ maybe (freshPosId $ idSeq globals) return maybeId
    when (isNothing maybeId) $
      liftSTtoIO $ BH.insert (graphMap globals) (decodeFullStack dest) actualId
    liftIO $ appendFile transFile $ T.pack $ "\n" ++ unwords [show fromId,  show actualId, show (fromRational prob_ :: Float)]
    if isNothing maybeId
      then return (Just dest)
      else return Nothing
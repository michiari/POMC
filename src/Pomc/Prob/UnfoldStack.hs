{-# LANGUAGE DeriveGeneric, DeriveAnyClass #-}

{- |
   Module      : Pomc.Prob.ProbUtils.hs
   Copyright   : 2023-2025 Francesco Pontiggia
   License     : MIT
   Maintainer  : Francesco Pontiggia
-}

module Pomc.Prob.UnfoldStack ( showFlatModel
                           ) where
import Prelude hiding(appendFile)
import Pomc.Encoding (nat)
import Pomc.Prec (Prec(..))
import Pomc.Z3T (liftSTtoIO)
import Pomc.PropConv (APType)
import Pomc.Potl (Formula(..), Prop (Prop, End))
import Pomc.SatUtil(freshPosId)
import qualified Pomc.Encoding as E

import Data.Hashable
import qualified Data.HashTable.ST.Basic as BH
import qualified Data.Set as Set

import Data.STRef (STRef, newSTRef, readSTRef)
import Pomc.LogUtils (MonadLogger, logInfoN)
import Data.Maybe (fromJust, isNothing, catMaybes)
import Control.Monad.ST (RealWorld)
import Control.Monad.IO.Class (MonadIO (liftIO))
import Data.Char (isLower, toLower)
import Data.Text.IO (appendFile)
import qualified Data.Text as T
import Control.Monad (when)
import Pomc.Prob.ProbUtils

-- a basic open-addressing hashtable using linear probing
-- s = thread state, k = key, v = value.

-------------------------------------------------------------------------------
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

decodeFullStack :: (StateId state, [Stack state]) -> (Int,[(Int,Int)])
decodeFullStack (s1, s) = (getId s1, map dec s)
  where dec Nothing = (0,0)
        dec (Just (i, s2)) = (nat i, getId s2)

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
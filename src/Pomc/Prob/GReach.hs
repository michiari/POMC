{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{- |
   Module      : Pomc.GReach
   Copyright   : 2023 Francesco Pontiggia
   License     : MIT
   Maintainer  : Francesco Pontiggia
-}

module Pomc.Prob.GReach ( GRobals(..)
                        , Delta(..)
                        , WeightedGRobals(..)
                        , newGRobals
                        , reachableStates
                        , showGrobals
                        , weightQuerySCC
                        , freezeSuppEnds
                        ) where

import Pomc.Prob.ProbUtils (Prob, EqMapNumbersType, Stats(..))
import Pomc.Prob.FixPoint
import Pomc.Prob.ProbEncoding (ProbEncodedSet, ProBitencoding)
import qualified Pomc.Prob.ProbEncoding as PE
import Pomc.Z3T (liftSTtoIO)

import Pomc.TimeUtils (startTimer, stopTimer)
import Pomc.LogUtils (MonadLogger, logDebugN, logInfoN)
import Pomc.Encoding (BitEncoding)
import Pomc.Prec (Prec(..))
import Pomc.Check(EncPrecFunc)
import Pomc.Prob.OVI (ovi, oviToRational, defaultOVISettingsDouble, OVIResult(..))

import Pomc.SatUtil

import Pomc.IOStack(IOStack)
import qualified Pomc.IOStack as IOGS

import Pomc.SetMap (SetMap)
import qualified Pomc.SetMap as SM

import Pomc.MapMap (MapMap)
import qualified Pomc.MapMap as MM

import qualified Pomc.IOMapMap as IOMM

import Data.IntSet(IntSet)
import qualified Data.IntSet as IntSet

import qualified Data.IntMap as Map


import qualified Data.Map as GeneralMap

import Data.Vector(Vector)
import qualified Data.Vector as V

import Data.Set(Set)
import qualified Data.Set as Set

import Control.Monad.ST (ST, RealWorld)
import qualified Control.Monad.ST as ST
import Data.STRef (STRef, newSTRef, writeSTRef, readSTRef, modifySTRef')

import Control.Monad(unless, when, foldM, forM_, forM)
import Control.Monad.IO.Class (MonadIO(liftIO))

import Data.Maybe
import Data.Hashable(Hashable)
import Data.Bifunctor(first)

import qualified Data.HashTable.ST.Basic as BH
import qualified Data.HashTable.Class as BC
import qualified Data.HashTable.IO as HT

import qualified Data.Vector.Mutable as MV
import GHC.IO (stToIO)

import Data.IORef (IORef, modifyIORef', readIORef, modifyIORef')
import Data.Ratio (approxRational, (%))

import Control.Applicative ((<|>))

-- a basic open-addressing hashtable using linear probing
-- s = thread state, k = key, v = value.
type HashTable s k v = BH.HashTable s k v

-- global variables in the algorithms
data GRobals s state = GRobals
  { sIdGen :: SIdGen s state
  , visited :: HashTable s (Int,Int,Int) ProbEncodedSet -- we store the recorded sat set as well
  , suppStarts :: STRef s (SetMap s (Stack state))
  , suppEnds :: STRef s (MapMap s (StateId state) ProbEncodedSet) -- we store the formulae satisfied in the support
  , currentInitial :: STRef s Int -- stateId of the current initial state
  }

showGrobals :: (Show state) => GRobals s state -> ST s String
showGrobals grobals = do
  s1 <- SM.showSetMap =<< readSTRef (suppStarts grobals)
  s2 <- MM.showMapMap =<< readSTRef (suppEnds grobals)
  s3 <- concatMap show <$> BC.toList (visited grobals)
  return $ "SuppStarts: " ++ s1 ++ "---- SuppEnds: " ++ s2 ++ "---- Visited: " ++ s3

-- a type for the delta relation, parametric with respect to the type of the state
data Delta state = Delta
  { bitenc :: BitEncoding
  , proBitenc :: ProBitencoding
  , prec :: EncPrecFunc -- precedence function which replaces the precedence matrix
  , deltaPush :: state -> [(state, Prob)] -- deltaPush relation
  , deltaShift :: state -> [(state, Prob)] -- deltaShift relation
  , deltaPop :: state -> state -> [(state, Prob)] -- deltapop relation
  , consistentFilter :: state -> Bool
  }

newGRobals :: ST.ST s (GRobals s state)
newGRobals = do
  newSig <- initSIdGen
  emptyVisited <- BH.new
  emptySuppStarts <- SM.empty
  emptySuppEnds <- MM.empty
  noInitial <- newSTRef (-1 :: Int)
  return $ GRobals { sIdGen = newSig
                   , visited = emptyVisited
                   , suppStarts = emptySuppStarts
                   , suppEnds = emptySuppEnds
                   , currentInitial = noInitial
                   }

reachableStates :: (SatState state, Eq state, Hashable state, Show state)
   => GRobals s state
   -> Delta state -- delta relation of the opa
   -> state -- current state
   -> ST s [(state, ProbEncodedSet)]
reachableStates globals delta state = do
  q <- wrapState (sIdGen globals) state
  currentSuppEnds <- MM.lookup (suppEnds globals) (getId q)
  if not (null currentSuppEnds)
    then return $ filter ((consistentFilter delta) . fst) . map (first getState) $ currentSuppEnds
    else do
      writeSTRef (currentInitial globals) (getId q)
      let newStateSatSet = PE.encodeSatState (proBitenc delta) state
      BH.insert (visited globals) (decode (q,Nothing)) newStateSatSet
      reach globals delta (q,Nothing) newStateSatSet
      updatedSuppEnds <- MM.lookup (suppEnds globals) (getId q)
      return $ filter ((consistentFilter delta) . fst) .  map (first getState) $ updatedSuppEnds

reach :: (SatState state, Eq state, Hashable state, Show state)
      => GRobals s state -- global variables of the algorithm
      -> Delta state -- delta relation of the opa
      -> (StateId state, Stack state) -- current semiconfiguration
      -> ProbEncodedSet -- current satset
      -> ST s ()
reach globals delta (q,g) pathSatSet = do
  let qState = getState q
      qProps = getStateProps (bitenc delta) qState
      precRel = (prec delta) (fst . fromJust $ g) qProps
      cases i
        -- semiconfigurations with empty stack but not the initial one
        | (isNothing g) && (getId q /= i) = do
            unless ((consistentFilter delta) qState) $ error $ "inconsistent AugState in a push with empty stack in GReach " ++  show qState

        -- this case includes the initial push
        | (isNothing g) || (precRel == Just Yield ) = do
            -- sanity check
            unless ((consistentFilter delta) qState) $ error $ "inconsistent AugState in a push in GReach " ++  show qState ++ "; " ++ show g ++ ";\n\n\nPREC " ++ show precRel
            reachPush globals delta q g qState pathSatSet

        | precRel == Just Equal = do
            unless ((consistentFilter delta) qState) $ error $ "inconsistent AugState in a shift in GReach " ++  show qState
            reachShift globals delta q g qState pathSatSet

        | precRel == Just Take =
            reachPop globals delta q g qState pathSatSet

        | otherwise = return ()
  iniId <- readSTRef (currentInitial globals)
  cases iniId

reachPush :: (SatState state, Eq state, Hashable state, Show state)
  => GRobals s state
  -> Delta state
  -> StateId state
  -> Stack state
  -> state
  -> ProbEncodedSet
  -> ST s ()
reachPush globals delta q g qState pathSatSet =
  let qProps = getStateProps (bitenc delta) qState
      doPush p = reachTransition globals delta Nothing Nothing (p, Just (qProps, q))
      isConsistentOrPop p = let s = getState p in (isJust g && prec delta (fst . fromJust $ g) (getStateProps (bitenc delta) $ s) == Just Take) || ((consistentFilter delta) s)
  in do
    SM.insert (suppStarts globals) (getId q) g
    newStates <- wrapStates (sIdGen globals) $ map fst $ (deltaPush delta) qState
    mapM_ doPush newStates
    currentSuppEnds <- MM.lookup (suppEnds globals) (getId q)
    mapM_ (\(s, supportSatSet) -> reachTransition globals delta (Just pathSatSet) (Just supportSatSet) (s,g))
      $ filter (isConsistentOrPop . fst) currentSuppEnds

reachShift :: (SatState state, Eq state, Hashable state, Show state)
      => GRobals s state
      -> Delta state
      -> StateId state
      -> Stack state
      -> state
      -> ProbEncodedSet
      -> ST s ()
reachShift globals delta _ g qState pathSatSet =
  let qProps = getStateProps (bitenc delta) qState
      doShift p = reachTransition globals delta (Just pathSatSet) Nothing (p, Just (qProps, snd . fromJust $ g))
  in do
    newStates <- wrapStates (sIdGen globals) $ map fst $ (deltaShift delta) qState
    mapM_ doShift newStates

reachPop :: (SatState state, Eq state, Hashable state, Show state)
    => GRobals s state
    -> Delta state
    -> StateId state
    -> Stack state
    -> state
    -> ProbEncodedSet
    -> ST s ()
reachPop globals delta _ g qState pathSatSet =
  let gState = getState . snd . fromJust $ g
      doPop p =
        let r = snd . fromJust $ g
            pState = getState p
            pProps = getStateProps (bitenc delta) pState
            isConsistentOrPop g' = (isJust g' && prec delta (fst . fromJust $ g') pProps == Just Take) || ((consistentFilter delta) pState)
            closeSupports g' = when (isConsistentOrPop g') $ do 
                  lcSatSet <- fromJust <$> BH.lookup (visited globals) (decode (r,g'))
                  reachTransition globals delta (Just lcSatSet) (Just pathSatSet) (p, g')
        in do
          MM.insertWith (suppEnds globals) (getId r) PE.union p pathSatSet
          currentSuppStarts <- SM.lookup (suppStarts globals) (getId r)
          mapM_ closeSupports currentSuppStarts
  in do
    newStates <- wrapStates (sIdGen globals) $ map fst $
      (deltaPop delta) qState gState
    mapM_  doPop newStates

-- handling the transition to a new semiconfiguration
reachTransition :: (SatState state, Eq state, Hashable state, Show state)
                 => GRobals s state
                 -> Delta state
                 -> Maybe ProbEncodedSet -- the SatSet established on the path so far
                 -> Maybe ProbEncodedSet -- the SatSet of the edge (Nothing if it is not a Support edge)
                 -> (StateId state, Stack state) -- to semiconf
                 -> ST s ()
reachTransition globals delta pathSatSet mSuppSatSet dest =
  let -- computing the new set of sat formulae for the current path in the chain
    newStateSatSet = PE.encodeSatState (proBitenc delta) (getState . fst $ dest)
    newPathSatSet = PE.unions (newStateSatSet : catMaybes [pathSatSet, mSuppSatSet])
    decodedDest = decode dest
  in do
  maybeSatSet <- BH.lookup (visited globals) decodedDest
  if isNothing maybeSatSet
    then do
      -- dest semiconf has not been visited so far
      BH.insert (visited globals) decodedDest newPathSatSet
      reach globals delta dest newPathSatSet
    else do
      let recordedSatSet = fromJust maybeSatSet
      let augmentedPathSatSet = PE.unions (recordedSatSet : catMaybes [pathSatSet, mSuppSatSet])
      unless (recordedSatSet `PE.subsumes` augmentedPathSatSet) $ do
        -- dest semiconf has been visited, but with a set of sat formulae that does not subsume the current ones
        BH.insert (visited globals) decodedDest augmentedPathSatSet
        reach globals delta dest augmentedPathSatSet

freezeSuppEnds :: GRobals RealWorld state -> IO (Vector (Set (StateId state)))
freezeSuppEnds globals = stToIO $ do
  computedSuppEnds <- readSTRef (suppEnds globals)
  V.generateM (MV.length computedSuppEnds) (fmap GeneralMap.keysSet . MV.unsafeRead computedSuppEnds)

type SuccessorsPopContexts = IntSet

data WeightedGRobals state = WeightedGRobals
  { idSeq      :: IORef Int
  , graphMap   :: HT.BasicHashTable (Int,Int,Int) Int
  , sStack     :: IOStack (StateId state, Stack state)
  , bStack     :: IOStack Int
  , iVector    :: HT.BasicHashTable Int Int
  , successorsCntxs :: HT.BasicHashTable Int IntSet
  , upperEqMap :: AugEqMap EqMapNumbersType
  , lowerEqMap :: AugEqMap EqMapNumbersType
  , actualEps :: IORef EqMapNumbersType
  , stats :: STRef RealWorld Stats
  }

-- compute weigths of a support transition
weightQuerySCC :: (MonadIO m, MonadLogger m, SatState state, Eq state, Hashable state, Show state)
               => WeightedGRobals state
               -> SIdGen RealWorld state
               -> Delta state -- delta relation of the augmented opa
               -> Vector (Set(StateId state))
               -> state -- current state
               -> state -- target state
               -> m (Prob, Prob)
weightQuerySCC globals sIdGen delta supports current target = do
  q <- liftSTtoIO $ wrapState sIdGen current
  let semiconf = (q, Nothing)
  targetState <- liftSTtoIO $ wrapState sIdGen target
  maybeSemiconfId <- liftIO $ HT.lookup (graphMap globals) (decode semiconf)

  actualId <- case maybeSemiconfId of
    Just scId -> do
      liftIO $ encodeInitialPush globals sIdGen delta q Nothing scId (getId targetState)
      solveSCCQuery (IntSet.singleton scId) globals
      return scId
    Nothing -> do
      newId <- liftIO $ freshIOPosId (idSeq globals)
      liftIO $ HT.insert (graphMap globals) (decode semiconf) newId
      liftIO $ addtoPath globals semiconf newId
      _ <- dfs globals sIdGen delta supports semiconf (newId, getId targetState) True
      liftIO $ encodeInitialPush globals sIdGen delta q Nothing newId (getId targetState)
      solveSCCQuery (IntSet.singleton newId) globals
      return newId

  -- returning the computed values
  eps <- liftIO $ readIORef (actualEps globals)
  lb <- liftIO $ (\(PopEq d) -> approxRational (d - eps) eps) . fromJust <$> IOMM.lookupValue (fst $ lowerEqMap globals) actualId (-1)
  ub <- liftIO $ (\(PopEq d) -> approxRational (d + eps) eps) . fromJust <$> IOMM.lookupValue (fst $ upperEqMap globals) actualId (-1)
  -- cleaning the hashtable
  deleteFixpEq (lowerEqMap globals) (actualId, -1)
  deleteFixpEq (upperEqMap globals) (actualId, -1)
  deleteFixpEq (lowerEqMap globals) (actualId, -2)
  deleteFixpEq (upperEqMap globals) (actualId, -2)
  let truncatedLB = min 1 lb
      truncatedUB = min 1 ub

  logInfoN $ "Returning weights: " ++ show (truncatedLB, truncatedUB)
  when (lb > ub || lb > 1 || ub - lb > 1 % 50) $ error $ "unsound or too loose bounds on weights for this summary transition: " ++ show (lb,ub)
  return (truncatedLB, truncatedUB)

-- functions for Gabow algorithm
dfs :: (MonadIO m, MonadLogger m, SatState state, Eq state, Hashable state, Show state)
    => WeightedGRobals state
    -> SIdGen RealWorld state
    -> Delta state
    -> Vector (Set(StateId state))
    -> (StateId state, Stack state) -- current semiconf
    -> (Int, Int) -- target
    -> Bool
    -> m SuccessorsPopContexts
dfs globals sIdGen delta supports (q,g) (semiconfId, target) encodeNothing =
  let qState = getState q
      gState = getState . snd . fromJust $ g
      qProps = getStateProps (bitenc delta) qState
      precRel = (prec delta) (fst . fromJust $ g) qProps
      transitionCases
        -- semiconfigurations with empty stack but not the initial one
        | (isNothing g) && not encodeNothing = do
          unless ((consistentFilter delta) qState) $ error "semiconfigurations with empty stack but inconsistent states" 
          return IntSet.empty

        -- this case includes the initial push
        | (isNothing g) || precRel == Just Yield = do
          unless ((consistentFilter delta) qState) $ error "inconsistent state in a push"
          newPushStates <- liftSTtoIO $ wrapStates sIdGen $ map fst $ (deltaPush delta) qState
          forM_ newPushStates (\p -> follow (p, Just (qProps, q))) -- discard the result
          let isConsistentOrPop p = let s = getState p in (isJust g && prec delta (fst . fromJust $ g) (getStateProps (bitenc delta) $ s) == Just Take) || ((consistentFilter delta) s)
              newSupportStates = Set.toList . Set.filter isConsistentOrPop . fromJust $ (supports V.!? (getId q)) <|> (Just Set.empty)
          if isNothing g
            then return IntSet.empty
            else IntSet.unions <$> forM newSupportStates (\p -> follow (p, g))

        | precRel == Just Equal = do
          unless ((consistentFilter delta) qState) $ error "inconsistent state in a push"
          newShiftStates <- liftSTtoIO $ wrapStates sIdGen $ map fst $ (deltaShift delta) qState
          IntSet.unions <$> forM newShiftStates (\p -> follow (p, Just (qProps, snd . fromJust $ g)))

        | precRel == Just Take = IntSet.fromList <$>
            mapM (\(unwrapped, _) -> do p <- liftSTtoIO $ wrapState sIdGen unwrapped; return (getId p)) ((deltaPop delta) qState gState)

        | otherwise = return IntSet.empty

      cases nextSemiconf nSCId iVal
        | (iVal == 0) = do
            liftIO $ addtoPath globals nextSemiconf nSCId
            dfs globals sIdGen delta supports nextSemiconf (nSCId, target) False
        | (iVal < 0)  = liftIO $ lookupCntxs globals nSCId
        | (iVal > 0)  = liftIO $ merge globals nextSemiconf nSCId >> return IntSet.empty
        | otherwise = error "unreachable error"
      follow nextSemiconf = do
        nSCId <- liftIO $ lookupSemiconf globals nextSemiconf
        iVal <- liftIO $ lookupIValue globals nSCId
        cases nextSemiconf nSCId iVal

  in do
    popContxs <- transitionCases
    createComponent globals sIdGen delta supports popContxs semiconfId

lookupVar :: IntSet -> WeightedGRobals state -> (Int, Int, Int) -> Int ->  IO (Maybe ((Int,Int), Bool))
lookupVar sccMembers globals decoded rightContext = do
  maybeId <- HT.lookup (graphMap globals) decoded
  let id_ = fromJust maybeId
      varKey = (id_, rightContext)
      (_, a,b) = decoded
  when (isNothing maybeId) $ error $ "future semiconfs should have been already visited and inserted in the hashtable: " ++ show decoded
  when ((a,b) == (0,0) || rightContext == -1) $ error "semiconfs with empty stack should not be in the RHS of the equation system"
  previouslyEncoded <- containsEquation (lowerEqMap globals) varKey
  let cases
          | previouslyEncoded = return $ Just (varKey, True)
          | IntSet.notMember id_ sccMembers = return Nothing
          | otherwise = do 
              addFixpEq (lowerEqMap globals) varKey (PopEq 0) -- this equation is needed as a placeholder to avoid double encoding of the same variable
              -- since we do not keep track of whether a variable is currently in the buffer of "unencodedVars"
              return $ Just (varKey, False)
  cases

lookupIValue :: WeightedGRobals state -> Int -> IO Int
lookupIValue globals semiconfId = do
  maybeIval <- HT.lookup (iVector globals) semiconfId
  maybe (return 0) return maybeIval

lookupCntxs :: WeightedGRobals state -> Int -> IO IntSet
lookupCntxs globals semiconfId = do
    maybeCntxs <- HT.lookup (successorsCntxs globals) semiconfId
    maybe (return IntSet.empty) return maybeCntxs

lookupSemiconf :: WeightedGRobals state -> (StateId state, Stack state) -> IO Int
lookupSemiconf globals semiconf = do
  maybeId <- HT.lookup (graphMap globals) (decode semiconf)
  actualId <- maybe (freshIOPosId (idSeq globals)) return maybeId
  when (isNothing maybeId) $ HT.insert (graphMap globals) (decode semiconf) actualId
  return actualId

freshIOPosId :: IORef Int -> IO Int
freshIOPosId idSeq = do
  curr <- readIORef idSeq
  modifyIORef' idSeq (+1)
  return curr

addtoPath :: WeightedGRobals state -> (StateId state, Stack state) -> Int -> IO ()
addtoPath globals semiconf semiconfId = do
  IOGS.push (sStack globals) semiconf
  sSize <- IOGS.size $ sStack globals
  HT.insert (iVector globals) semiconfId sSize
  IOGS.push (bStack globals) sSize

merge ::  WeightedGRobals state -> (StateId state, Stack state) -> Int -> IO ()
merge globals _ semiconfId = do
  iVal <- lookupIValue globals semiconfId
  -- contract the B stack, that represents the boundaries between SCCs on the current path
  IOGS.popWhile_ (bStack globals) (iVal <)

createComponent :: (MonadIO m, MonadLogger m, SatState state, Eq state, Hashable state, Show state)
  => WeightedGRobals state
  -> SIdGen RealWorld state
  -> Delta state
  -> Vector (Set(StateId state))
  -> SuccessorsPopContexts
  -> Int
  -> m SuccessorsPopContexts
createComponent globals sIdGen delta supports popContxs semiconfId = do
  topB <- liftIO . IOGS.peek $ bStack globals
  iVal <- liftIO $ lookupIValue globals semiconfId
  let createC = liftIO $ do
        IOGS.pop_ (bStack globals)
        sSize <- IOGS.size $ sStack globals
        poppedSemiconfs <- IOGS.multPop (sStack globals) (sSize - iVal + 1) -- the last one is to gn
        forM poppedSemiconfs $ \s -> do
          actualId <- fromJust <$> HT.lookup (graphMap globals) (decode s)
          HT.insert (iVector globals) actualId (-1)
          HT.insert (successorsCntxs globals) actualId popContxs
          return (s, actualId)
      doEncode poppedSemiconfs = do
        let toEncode = [(s, semiconfId_, rc) | (s, semiconfId_) <- poppedSemiconfs, rc <- IntSet.toList popContxs]
            sccMembers = IntSet.fromList . map snd $ poppedSemiconfs
        insertedVars <- liftIO $ map (snd . fromJust) <$> forM toEncode (\(s, _, rc) -> lookupVar sccMembers globals (decode s) rc)
        when (or insertedVars) $ error "inserting a variable that has already been encoded"
        liftIO $ forM_ toEncode $ \v -> encode v globals sIdGen delta supports sccMembers
        solveSCCQuery sccMembers globals
        return popContxs
      doNotEncode _ = do
          liftSTtoIO $ modifySTRef' (stats globals) $ \s@Stats{sccCountQuant = acc} -> s{sccCountQuant = acc + 1}
          return popContxs
      cases
        | iVal /= topB = return popContxs
        | not (IntSet.null popContxs) = createC >>= doEncode -- can reach a pop
        | otherwise = createC >>= doNotEncode -- cannot reach a pop
  cases


-- encode = generate the set of equation for pairs (semiconf, rightContext) to determine fraction f
encode :: (SatState state, Eq state, Hashable state, Show state)
  => ((StateId state, Stack state), Int, Int)
  -> WeightedGRobals state
  -> SIdGen RealWorld state
  -> Delta state
  -> Vector (Set(StateId state))
  -> IntSet
  -> IO ()
encode ((q,g), semiconfId, rightContext) globals sIdGen delta supports sccMembers =
  let qState = getState q
      gState = getState . snd . fromJust $ g
      qProps = getStateProps (bitenc delta) qState
      precRel = (prec delta) (fst . fromJust $ g) qProps
      cases
        | precRel == Just Yield =
            encodePush globals sIdGen delta supports q g qState (semiconfId, rightContext) sccMembers

        | precRel == Just Equal =
            encodeShift globals sIdGen delta supports q g qState (semiconfId, rightContext) sccMembers

        | precRel == Just Take = do
            distr <- mapM (\(unwrapped, prob_) -> do p <- stToIO $ wrapState sIdGen unwrapped; return (getId p, prob_)) $ (deltaPop delta) qState gState
            let e = Map.findWithDefault 0 rightContext (Map.fromList distr)
            addFixpEq (lowerEqMap globals) (semiconfId, rightContext) $ PopEq $ fromRational e
            liftSTtoIO $ modifySTRef' (stats globals) $ \s@Stats{equationsCountQuant = acc} -> s{equationsCountQuant = acc + 1}
            addFixpEq (upperEqMap globals) (semiconfId, rightContext) $ PopEq $ fromRational e
            -- logDebugN $ "Encoding PopSemiconf: " ++ show (semiconfId, rightContext) ++ " = PopEq " ++ show e

        | otherwise = fail "unexpected prec rel"
  in cases

encodePush :: (SatState state, Eq state, Hashable state, Show state)
  => WeightedGRobals state
  -> SIdGen RealWorld state
  -> Delta state
  -> Vector (Set(StateId state))
  -> StateId state
  -> Stack state
  -> state
  -> (Int, Int)
  -> IntSet
  -> IO ()
encodePush globals sIdGen delta supports q g qState (semiconfId, rightContext) sccMembers =
  let isConsistentOrPop p = let s = getState p in (isJust g && prec delta (fst . fromJust $ g) (getStateProps (bitenc delta) $ s) == Just Take) || ((consistentFilter delta) s)
      suppEnds = Set.toList . Set.filter isConsistentOrPop . fromJust $ (supports V.!? getId q) <|> (Just Set.empty)
      qProps = getStateProps (bitenc delta) qState
      closeSupports pushDest (unencodedVars, terms) suppId =
        let suppDest = (suppId, g)
            varsList = [(pushDest, getId suppId), (suppDest, rightContext)]
        in do
          maybeTerms <- mapM (\(sc, rc) -> lookupVar sccMembers globals (decode sc) rc) varsList
          let newUnencoded = [ (sc, scId, rc) | ((sc, _), Just ((scId, rc), False)) <- zip varsList maybeTerms]
                           ++ unencodedVars
          if any isNothing maybeTerms
            then return (newUnencoded, terms)
            else return (newUnencoded, map (fst . fromJust) maybeTerms:terms)

      pushEnc (newVars, terms) (p, prob_) =
        let dest = (p, Just (qProps, q)) in do
          (unencodedVars, varTerms) <- foldM (closeSupports dest) ([], []) suppEnds
          return (unencodedVars ++ newVars, (map (\[v1, v2] -> (prob_, v1, v2)) varTerms):terms)

  in do
    newStates <- mapM (\(unwrapped, prob_) -> do p <- stToIO $ wrapState sIdGen unwrapped; return (p,prob_)) $ (deltaPush delta) qState
    (unencodedVars, terms) <- foldM pushEnc ([], []) newStates
    let emptyPush = all null terms
        pushEq | emptyPush = PopEq 0
               | otherwise = PushEq $ concat terms
    addFixpEq (lowerEqMap globals) (semiconfId, rightContext) pushEq
    liftSTtoIO $ modifySTRef' (stats globals) $ \s@Stats{equationsCountQuant = acc} -> s{equationsCountQuant = acc + 1}
    addFixpEq (upperEqMap globals) (semiconfId, rightContext) pushEq
    -- logDebugN $ "Encoding Push: " ++ show terms
    forM_ unencodedVars $ \v -> encode v globals sIdGen delta supports sccMembers

encodeInitialPush :: (SatState state, Eq state, Hashable state, Show state)
    => WeightedGRobals state
    -> SIdGen RealWorld state
    -> Delta state
    -> StateId state
    -> Stack state
    -> Int
    -> Int
    -> IO ()
encodeInitialPush globals sIdGen delta q _ semiconfId suppId  =
    let qState = getState q
        qProps = getStateProps (bitenc delta) qState
        pushEnc terms (p, prob_) =
          let dest = (p, Just (qProps, q)) in do
            pushId <- fromJust <$> HT.lookup (graphMap globals) (decode dest)
            present <- containsEquation (lowerEqMap globals) (pushId, suppId)
            if present
              then return $ (prob_, (pushId, suppId), (semiconfId, -2)):terms
              else return terms
    in do
      newStates <- mapM (\(unwrapped, prob_) -> do p <- stToIO $ wrapState sIdGen unwrapped; return (p,prob_)) $ (deltaPush delta) qState
      terms <- foldM pushEnc [] newStates
      addFixpEq (lowerEqMap globals) (semiconfId, -1) $ PushEq terms
      addFixpEq (upperEqMap globals) (semiconfId, -1) $ PushEq terms
      -- logDebugN $ "Encoding initial push:" ++ show terms
      addFixpEq (lowerEqMap globals) (semiconfId, -2) $ PopEq (1 :: Double)
      liftSTtoIO $ modifySTRef' (stats globals) $ \s@Stats{equationsCountQuant = acc} -> s{equationsCountQuant = acc + 1}
      addFixpEq (upperEqMap globals) (semiconfId, -2) $ PopEq (1 :: Double)

encodeShift :: (SatState state, Eq state, Hashable state, Show state)
  => WeightedGRobals state
  -> SIdGen RealWorld state
  -> Delta state
  -> Vector (Set(StateId state))
  -> StateId state
  -> Stack state
  -> state
  -> (Int, Int)
  -> IntSet
  -> IO ()
encodeShift globals sIdGen delta supports _ g qState (semiconfId, rightContext) sccMembers =
  let qProps = getStateProps (bitenc delta) qState
      shiftEnc (newVars, terms) (p, prob_) = do
        let dest = (p, Just (qProps, snd . fromJust $ g))
        maybeTerm <- lookupVar sccMembers globals (decode dest) rightContext
        if isNothing maybeTerm
          then return (newVars, terms)
          else let
            (varKey, alreadyEncoded) = fromJust maybeTerm
            newUnencoded = if alreadyEncoded then newVars else (dest, fst varKey, snd varKey):newVars
          in return ( newUnencoded,(prob_, varKey):terms)
  in do
    newStates <- mapM (\(unwrapped, prob_) -> do p <- stToIO $ wrapState sIdGen unwrapped; return (p,prob_)) $ (deltaShift delta) qState
    (unencodedVars, terms) <- foldM shiftEnc ([], []) newStates
    let shiftEq | null terms = error "shift semiconfs should go somewhere!"
                | otherwise = ShiftEq terms
    addFixpEq (lowerEqMap globals) (semiconfId, rightContext) shiftEq
    liftSTtoIO $ modifySTRef' (stats globals) $ \s@Stats{equationsCountQuant = acc} -> s{equationsCountQuant = acc + 1}
    addFixpEq (upperEqMap globals) (semiconfId, rightContext) shiftEq
    -- logDebugN $ "Encoding shift: " ++ show (semiconfId, rightContext) ++ " = ShiftEq " ++ show terms
    forM_ unencodedVars $ \v -> encode v globals sIdGen delta supports sccMembers

solveSCCQuery :: (MonadIO m, MonadLogger m, Eq state, Hashable state, Show state)
              => IntSet -> WeightedGRobals state -> m ()
solveSCCQuery sccMembers globals = do
  let sccLen = IntSet.size sccMembers
      epsVar = actualEps globals
      lEqMap = lowerEqMap globals
      uEqMap = upperEqMap globals

  currentEps <- liftIO $ readIORef epsVar
  let iterEps = min defaultEps $ currentEps * currentEps

  -- preprocessing to solve variables that do not need ovi
  _ <- preprocessApproxFixp lEqMap iterEps (sccLen + 1)
  (updatedVars, unsolvedVars) <- preprocessApproxFixp uEqMap iterEps (sccLen + 1)

  liftSTtoIO $ modifySTRef' (stats globals) $ \s@Stats{sccCountQuant = acc} -> s{sccCountQuant = acc + 1}
  liftSTtoIO $ modifySTRef' (stats globals) $ \s@Stats{largestSCCSemiconfsCountQuant = acc} -> s{largestSCCSemiconfsCountQuant = max acc (IntSet.size sccMembers)}

  -- lEqMap and uEqMap should be the same here
  unless (null unsolvedVars) $ do
    liftSTtoIO $ modifySTRef' (stats globals) $ \s@Stats{nonTrivialEquationsCountQuant = acc} -> s{nonTrivialEquationsCountQuant = acc + length unsolvedVars}
    liftSTtoIO $ modifySTRef' (stats globals) $ \s@Stats{ largestSCCNonTrivialEqsCountQuant = acc } -> s{ largestSCCNonTrivialEqsCountQuant = max acc (length updatedVars) }
    startWeights <- startTimer

    -- computing lower bounds
    approxVec <- approxFixp lEqMap iterEps defaultMaxIters

    -- computing upper bounds
    logDebugN "Running OVI to compute an upper bound to the equation system"
    oviRes <- ovi defaultOVISettingsDouble uEqMap

    rCertified <- oviToRational defaultOVISettingsDouble uEqMap oviRes
    unless rCertified $ error "cannot deduce a rational certificate for this SCC when computing fraction f"

    unless (oviSuccess oviRes) $ error "OVI was not successful in computing an upper bounds on the fraction f"

    tWeights <- stopTimer startWeights rCertified
    liftSTtoIO $ modifySTRef' (stats globals) (\s -> s { quantWeightTime = quantWeightTime s + tWeights })

    -- updating lower bounds 
    liftIO $ HT.mapM_ (\(varKey, p) -> addFixpEq lEqMap varKey (PopEq p)) approxVec

    -- updating upper bounds
    liftIO $ HT.mapM_ (\(varKey, p) -> addFixpEq uEqMap varKey (PopEq p)) (oviUpperBound oviRes)

    upperBound <- liftIO $ HT.toList (oviUpperBound oviRes)
    logDebugN $ "Computed upper bounds: " ++ show upperBound

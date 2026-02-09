{-# LANGUAGE DeriveGeneric #-}
{- |
   Module      : Pomc.Prob.GQuantitative
   Copyright   : 2026 Francesco Pontiggia
   License     : MIT
   Maintainer  : Francesco Pontiggia
-}
module Pomc.Prob.GQuantitative ( GNode(..)
                        , quantitativeModelCheck
                        ) where
import Pomc.SatUtil(SIdGen, freshPosId)
import Pomc.TimeUtils (startTimer, stopTimer)
import Pomc.LogUtils (MonadLogger, logInfoN)
import qualified Pomc.SatUtil as SU
import Pomc.State(State(..))
import Pomc.Prec (Prec(..))
import Pomc.Potl(Formula(..))
import Pomc.PropConv(APType)
import Pomc.Check (EncPrecFunc)
import qualified Pomc.Encoding as E
import Pomc.Z3T
import qualified Pomc.GStack as GS
import qualified Pomc.CustoMap as CM

import qualified Pomc.Prob.GQualitative as GQual
import Pomc.Prob.GUtil
import Pomc.Prob.ProbUtils hiding (sIdMap, SIdGen)
import qualified Pomc.Prob.GReach as GR
import qualified Pomc.Prob.GWeight as GW
import Pomc.Prob.SupportGraph(GraphNode(..), SupportGraph)

import qualified Data.Strict.IntMap as StrictIntMap
import qualified Data.Strict.Map as StrictMap

import qualified Data.Set as Set
import qualified Data.IntSet as IntSet

import Data.Vector(Vector, (!))
import qualified Data.Vector as V
import Data.Ratio ((%))

import Control.Monad.IO.Class (MonadIO(liftIO))
import Control.Monad (when, forM_, foldM, forM)
import Control.Monad.ST (RealWorld)

import Data.STRef (STRef, newSTRef, readSTRef, modifySTRef')
import Data.Maybe (fromJust, isNothing, catMaybes)

import Data.Hashable
import qualified Data.HashTable.IO as HT
import qualified Data.HashTable.ST.Basic as BH

import Z3.Monad

-- quantitative model checking --
-- requires: the initial semiconfiguration has id 0, and it is not reachable from itself
-- pstate: a parametric type for states of the input popa
quantitativeModelCheck :: (MonadIO m, MonadFail m, MonadLogger m, Ord pstate, Hashable pstate, Show pstate)
  => DeltaWrapper pstate
  -> Formula APType -- phi: input formula to check
  -> [State] -- initial states of the phiOpa
  -> SupportGraph pstate
  -> Vector Bool
  -> Vector Prob
  -> Vector Prob
  -> StrictMap.Map pstate Int
  -> STRef RealWorld Stats
  -> Pomc.Prob.ProbUtils.Solver
  -> m (Prob, Prob)
quantitativeModelCheck delta phi phiInitials suppGraph pendVector lbPendProbs ubPendProbs sIdMap stats solv = do
  startGGTime <- startTimer

  -- globals data structures for qualitative model checking
  -- -1 is reserved for useless (i.e. single node) SCCs
  gGlobals <- liftSTtoIO $ do
    newIdSequence <- newSTRef (0 :: Int)
    let numPendingSemiconfs = foldl (flip ((+) . fromEnum)) 0 pendVector
    emptyGGraphMap <- BH.newSized numPendingSemiconfs
    emptyGGraph <- CM.emptySized numPendingSemiconfs
    emptyGRGlobals <- GR.newGReachGlobals
    sccCounter   <- newSTRef (-2 :: Int)
    newSS        <- GS.new
    newBS        <- GS.new
    newFoundSCCs <- newSTRef StrictIntMap.empty
    return GGlobals { idSeq = newIdSequence
                    , ggraphMap = emptyGGraphMap
                    , gGraph = emptyGGraph
                    , grGlobals = emptyGRGlobals
                    , sStack = newSS
                    , bStack = newBS
                    , cGabow = sccCounter
                    , bottomHSCCs = newFoundSCCs
                    }
  logInfoN "Building and Analyzing graph G..."
  let iniGn = suppGraph ! 0
      iniLabel = getLabel . fst . semiconf $ iniGn
      isPhiState = E.member (bitenc delta) phi . current
      phiInitialsFilter s = iniLabel == E.extractInput (bitenc delta) (current s)
      initialStates = filter phiInitialsFilter phiInitials

  phiInitialGNodesIdxs <- catMaybes <$> forM initialStates (\s -> liftSTtoIO $ do
      -- create a new GNode 
    newId <-  freshPosId (idSeq gGlobals)
    BH.insert (ggraphMap gGlobals) (gnId iniGn, s) newId
    let node = GNode {gId= newId, graphNode = gnId iniGn, phiNode = s, edges = Set.empty, iValue = 0, descSccs = IntSet.empty}
    CM.insert (gGraph gGlobals) newId node
    -- we always set fromPhi to False because we want to keep track of ALL BSCCs of subgraph H, contrarily to qualitative mc.
    updatedNode <- GQual.addtoPath gGlobals node (Internal 0 newId) 
    _ <- GQual.dfs suppGraph gGlobals delta (pendVector V.!) False sIdMap updatedNode
    if isPhiState s
      then return (Just newId)
      else return Nothing)

  hSCCs <- liftSTtoIO $ StrictIntMap.keysSet <$> readSTRef (bottomHSCCs gGlobals)

  -- some statistics about graph G
  logInfoN "Computed qualitative model checking..."
  tGG <- stopTimer startGGTime hSCCs
  liftSTtoIO $ modifySTRef' stats (\s -> s {gGraphTime = tGG })
  idx <- liftSTtoIO . readSTRef . idSeq $ gGlobals
  g <- CM.take idx <$> liftSTtoIO (readSTRef (gGraph gGlobals))
  freezedGGraph <- liftSTtoIO $ V.freeze g
  liftSTtoIO $ modifySTRef' stats (\s -> s {gGraphSize = idx})
  logInfoN $ "Graph G has " ++ show idx ++ " nodes."

  -- bottomString <- show <$> readSTRef (bottomHSCCs gGlobals)
  -- gString <- CM.showMap computedGraph
  -- logDebugN gString
  -- logDebugN bottomString

  -- computing the probability of satisfying the temporal formula
  let isInH = not . IntSet.null . IntSet.intersection hSCCs . descSccs
      insert var Nothing         = (Just [var], ())
      insert var (Just old_vars) = (Just (var:old_vars), ())

  evalZ3TWith (Just QF_LRA) stdOpts $ do
    -- generate all variables and add them to two hashtables
    newlMap <- liftSTtoIO BH.new
    newlGroupedMap <- liftSTtoIO BH.new
    newuMap <- liftSTtoIO BH.new
    newuGroupedMap <- liftSTtoIO BH.new
    forM_ freezedGGraph $ \g -> when (isInH g) $ do
      newlVar <- mkFreshRealVar (show (gId g) ++ "L")
      newuVar <- mkFreshRealVar (show (gId g) ++ "U")
      liftIO $ HT.insert newlMap (gId g) newlVar
      liftIO $ HT.insert newuMap (gId g) newuVar
      liftIO $ HT.mutate newlGroupedMap (graphNode g) (insert newlVar)
      liftIO $ HT.mutate newuGroupedMap (graphNode g) (insert newuVar)

    logInfoN "Generated z3 vars for encoding (2) from [Etessami and Yannakakis, TOCL 2012,Lemmas 34 and 35]"

    -- preparing the global variables for the computation of the fractions f
    freezedSuppEnds <- liftIO $ GR.freezeSuppEnds (grGlobals gGlobals)
    freezedSuppStarts <- liftIO $ GR.freezeSuppStarts (grGlobals gGlobals)

    lenHashtables <- liftSTtoIO $ GR.nrSemiconfs (grGlobals gGlobals)
    gWeightGlobals <- GW.newGWeightGlobals lenHashtables stats

    logInfoN "Encoding conditions (2b) and (2c) from [Etessami and Yannakakis, TOCL 2012,Lemmas 34 and 35]"
    -- encodings (2b) and (2c)
    encs1 <- concat <$> mapM
      (\gNode -> encode
          gWeightGlobals (GR.sIdGen (grGlobals gGlobals)) freezedSuppStarts freezedSuppEnds delta
          (newlMap, newuMap) suppGraph freezedGGraph (prec delta) isInH gNode
          lbPendProbs ubPendProbs sIdMap (useNewton solv)
      ) (V.filter isInH freezedGGraph)

    logInfoN "Encoding conditions (2a) from [Etessami and Yannakakis, TOCL 2012,Lemmas 34 and 35]"
    -- encoding (2a) for lower bounds
    groupedlMaptoList <- liftIO (HT.toList newlGroupedMap)
    encs2 <- foldM (\acc (_, vList) -> do
        vSum <- mkAdd vList
        lConstr1 <- mkLe vSum =<< mkRational (1 :: Prob)
        lConstr2 <- mkGe vSum =<< mkRational (1 - 1 % 100)
        eqString <- astToString lConstr1
        logInfoN $ "Asserting Sum equal 1: " ++ eqString
        return (lConstr1:lConstr2:acc)
      ) [] groupedlMaptoList

    -- encoding (2a) for upper bounds
    groupeduMaptoList <- liftIO (HT.toList newuGroupedMap)
    encs3 <- foldM (\acc (_, vList) -> do
      vSum <- mkAdd vList
      uConstr1 <- mkGe vSum =<< mkRational (1 :: Prob)
      eqString <- astToString uConstr1
      logInfoN $ "Asserting Sum equal 1: " ++ eqString
      uConstr2 <- mkLe vSum =<< mkRational (1 + 1 % 100)
      eqString <- astToString uConstr2
      logInfoN $ "Asserting Sum equal 1: " ++ eqString
      return (uConstr1:uConstr2:acc)
      ) [] groupeduMaptoList

    -- computing bounds on the probability to satisfy the given property
    let phiInitialGNodesIdxsinH = filter (isInH . (freezedGGraph V.!)) phiInitialGNodesIdxs
    philVars <- liftIO $ mapM  (fmap fromJust . HT.lookup newlMap) phiInitialGNodesIdxsinH
    phiuVars <- liftIO $ mapM  (fmap fromJust . HT.lookup newuMap) phiInitialGNodesIdxsinH

    sumlVar <- mkAdd philVars
    eqStringL <- astToString sumlVar
    logInfoN $ "Sum of interest (lower bound): " ++ eqStringL
    sumuVar <- mkAdd phiuVars
    eqStringU <- astToString sumuVar
    logInfoN $ "Sum of interest (upper bound): " ++ eqStringU

    startSol <- startTimer
    mapM_ assert encs1 >> mapM_ assert encs2 >> mapM_ assert encs3
    logInfoN "Calling Z3 to solve the linear program for quantitative model checking..."
    let parseResult (Sat, bounds) = fromJust bounds
        parseResult _ = error "the linear program for quantitative model checking has no solution."
    (lb, ub) <- parseResult <$> withModel (\model -> do
      l <- extractLowerProb . fromJust =<< eval model sumlVar
      u <- extractUpperProb . fromJust =<< eval model sumuVar
      logInfoN $ "Computed lower bound on the quantitative probability: " ++ show l
      logInfoN $ "Computed upper bound on the quantitative probability: " ++ show u
      return (l, u))

    tSol <- stopTimer startSol ub
    liftSTtoIO $ modifySTRef' stats (\s -> s { quantSolTime = quantSolTime s + tSol})
    return (lb, min 1 ub)

-- helpers for the Z3 encoding
-- every node of graph H is associated with a Z3 var
type TypicalVarMap = HT.BasicHashTable Int AST

encodeTransition :: MonadZ3 z3 => Prob -> Prob -> Prob -> AST -> z3 AST
encodeTransition prob_ num den toVar = do
  rtNum <- mkRational num
  rtProb_ <- mkRational prob_
  rtDen <- mkRational den
  mul <- mkMul $ rtProb_:rtNum:[toVar]
  mkDiv mul rtDen

encode :: (MonadZ3 z3, MonadFail z3, MonadLogger z3, Ord pstate, Hashable pstate, Show pstate)
  => GW.GWeightGlobals
  -> SIdGen RealWorld (AugState pstate)
  -> Vector [SU.Stack (AugState pstate)]
  -> Vector (Vector (SU.StateId (AugState pstate)))
  -> DeltaWrapper pstate
  -> (TypicalVarMap, TypicalVarMap)
  -> SupportGraph pstate
  -> Vector GNode
  -> EncPrecFunc
  -> (GNode -> Bool)
  -> GNode
  -> Vector Prob
  -> Vector Prob
  -> StrictMap.Map pstate Int
  -> Bool
  -> z3 [AST]
encode gwGlobals sIdGen suppStarts supports delta (lTypVarMap, uTypVarMap) suppGraph gGraph precFun isInH gNode pendProbsLB pendProbsUB sIdMap useNewton =
  let gn = suppGraph ! graphNode gNode
      (q,g) = semiconf gn
      qLabel = getLabel q
      precRel = precFun (fst . fromJust $ g) qLabel -- safe due to laziness
      cases
        -- this case includes the initial push
        | isNothing g || precRel == Just Yield =
            encodePush gwGlobals sIdGen suppStarts supports delta (lTypVarMap, uTypVarMap) suppGraph
              gGraph isInH gNode gn pendProbsLB pendProbsUB sIdMap useNewton

        | precRel == Just Equal =
            encodeShift (lTypVarMap, uTypVarMap) gGraph isInH gNode pendProbsLB pendProbsUB

        | otherwise = fail "unexpected prec rel"
  in cases

-- encoding helpers --
encodePush :: (MonadZ3 z3, MonadFail z3, MonadLogger z3, Ord pstate, Hashable pstate, Show pstate)
  => GW.GWeightGlobals
  -> SIdGen RealWorld (AugState pstate)
  -> Vector [SU.Stack (AugState pstate)]
  -> Vector (Vector(SU.StateId (AugState pstate)))
  -> DeltaWrapper pstate
  -> (TypicalVarMap, TypicalVarMap)
  -> SupportGraph pstate
  -> Vector GNode
  -> (GNode -> Bool)
  -> GNode
  -> GraphNode pstate
  -> Vector Prob
  -> Vector Prob
  -> StrictMap.Map pstate Int
  -> Bool
  -> z3 [AST]
encodePush gwGlobals sIdGen suppStarts supports delta (lTypVarMap, uTypVarMap) suppGraph gGraph isInH g gn pendProbsLB pendProbsUB sIdMap useNewton =
  let edgesInH = Set.toList . Set.filter (isInH . (gGraph V.!). toG) . edges $ g
      trivialSCC [] = error "there must be at least one edge in H"
      trivialSCC [e] = (toG e) == (gId g)
      trivialSCC _ = False

      pushEnc e = do
        let toIdx = toG e
        tolVar <- liftIO $ fromJust <$> HT.lookup lTypVarMap toIdx
        touVar <- liftIO $ fromJust <$> HT.lookup uTypVarMap toIdx
        let destG = gGraph ! toIdx
            -- push edges in the support Graph
            encodePushTrans = do
              lT <- encodeTransition (probInt e) (pendProbsLB ! (graphNode destG)) (pendProbsUB V.! (graphNode g)) tolVar
              uT <- encodeTransition (probInt e) (pendProbsUB ! (graphNode destG)) (pendProbsLB V.! (graphNode g)) touVar
              return [(lT, uT)]
            -- supports edges in the Support Graph
            supportGn = suppGraph V.! (graphNode destG)
            -- augmented states in the cross product
            leftContext = AugState (fst . semiconf $ gn) (phiNode g)
            rightContext = AugState (fst . semiconf $ supportGn) (phiNode destG)
            precRel = prec delta
            currentInput q = E.extractInput (bitenc delta) (current q)
            cDeltaPush (AugState (StateId _ q0 lab0) p0) =
              [ (AugState (StateId id1 q1 lab1) p1, prob_) |
                  (q1, lab1, prob_) <- (deltaPush delta) q0
                , p1 <- (phiDeltaPush delta) p0
                , (precRel lab0 lab1 == Just Take) || lab1 == currentInput p1
                , let id1 = sIdMap StrictMap.! q1
              ]
            cDeltaShift (AugState (StateId _ q0 lab0) p0) =
              [ (AugState (StateId id1 q1 lab1) p1, prob_) |
                  (q1, lab1, prob_) <- (deltaShift delta) q0
                , p1 <- (phiDeltaShift delta) p0
                , (precRel lab0 lab1 == Just Take) || lab1 == currentInput p1
                , let id1 = sIdMap StrictMap.! q1
              ]
            cDeltaPop (AugState (StateId _ q0 _) p0) (AugState (StateId _ q1 _) p1)  =
              [(AugState (StateId id2 q2 lab2) p2, prob_) |
                  (q2, lab2, prob_) <- (deltaPop delta) q0 q1
                ,  let id2 = sIdMap StrictMap.! q2
                ,  p2 <- (phiDeltaPop delta) p0 p1
              ]

            consistentFilter (AugState sId p0) = (getLabel sId) == currentInput p0
            cDelta = GW.Delta
              { GW.bitenc = bitenc delta
              , GW.proBitenc = proBitenc delta
              , GW.prec   = prec delta
              , GW.deltaPush = cDeltaPush
              , GW.deltaShift = cDeltaShift
              , GW.deltaPop = cDeltaPop
              , GW.consistentFilter = consistentFilter
              }
            encodeSupportTrans = do
              logInfoN $ "encountered a support transition - launching call to inner computation of fraction f from H node "
                ++ show (gId g) ++ " to H node " ++ show toIdx
              (lW, uW) <- GW.weightQuerySCC gwGlobals sIdGen cDelta suppStarts supports leftContext rightContext useNewton
              lT <- encodeTransition lW (pendProbsLB V.! (graphNode destG)) (pendProbsUB V.! (graphNode g)) tolVar
              uT <- encodeTransition uW (pendProbsUB V.! (graphNode destG)) (pendProbsLB V.! (graphNode g)) touVar
              return [(lT, uT)]
            cases
              | (SupportAndInternal {}) <- e = do
                  pushEncs <- encodePushTrans
                  suppEncs <- encodeSupportTrans
                  return (pushEncs ++ suppEncs)
              | (Internal _ _) <- e = encodePushTrans
              | (Support _ _) <- e = encodeSupportTrans
        cases
  in do
    -- a sanity check
    --unless (graphNode g == gnId gn) $ error "encodePush corresponding to non consistent pair GNode - graphNode"
    lvar <- liftIO $ fromJust <$> HT.lookup lTypVarMap (gId g)
    uvar <- liftIO $ fromJust <$> HT.lookup uTypVarMap (gId g)
    if trivialSCC edgesInH
      then do
        -- this would give an equation x = x, which has necessarily solution 1,
        -- otherwise it would violate uniqueness of solution
        -- this constraint is helpful to deal with bounds and approximations
        lEqOne <- mkEq lvar =<< mkRational (1 :: Prob)
        uEqOne <- mkEq uvar =<< mkRational (1 :: Prob)
        return [lEqOne, uEqOne]
      else do
        transitions <- concat <$> mapM pushEnc edgesInH
        lEq <- mkGe lvar =<< mkAdd (map fst transitions)
        uEq <- mkLe uvar =<< mkAdd (map snd transitions)
        soundness <- mkLe lvar uvar
        -- debugging
        eqLString <- astToString lEq
        logInfoN $ "Asserting Push/Support equation (lower bound): " ++ eqLString
        eqUString <- astToString uEq
        logInfoN $ "Asserting Push/Support equation (upper bound): " ++ eqUString
        return [lEq, uEq, soundness]

encodeShift :: (MonadZ3 z3, MonadLogger z3)
  => (TypicalVarMap, TypicalVarMap)
  -> Vector GNode
  -> (GNode -> Bool)
  -> GNode
  -> Vector Prob
  -> Vector Prob
  -> z3 [AST]
encodeShift (lTypVarMap, uTypVarMap) gGraph isInH g pendProbsLB pendProbsUB =
  let edgesInH = Set.toList . Set.filter (isInH . (gGraph V.!). toG) . edges $ g
      trivialSCC [] = error "there must be at least one edge in H"
      trivialSCC [e] = toG e == gId g
      trivialSCC _ = False
      shiftEnc (Internal prob_ toIdx) = do
        tolVar <- liftIO $ fromJust <$> HT.lookup lTypVarMap toIdx
        touVar <- liftIO $ fromJust <$> HT.lookup uTypVarMap toIdx
        let destG = gGraph V.! toIdx
        lT <- encodeTransition (prob_) (pendProbsLB V.! (graphNode destG)) (pendProbsUB V.! (graphNode g)) tolVar
        uT <- encodeTransition (prob_) (pendProbsUB V.! (graphNode destG)) (pendProbsLB V.! (graphNode g)) touVar
        return (lT, uT)
  in do
  -- a sanity check
  --unless (graphNode g == gnId gn) $ error "encodeShift encountered a non consistent pair GNode - graphNode"
  lvar <- liftIO $ fromJust <$> HT.lookup lTypVarMap (gId g)
  uvar <- liftIO $ fromJust <$> HT.lookup uTypVarMap (gId g)
  if trivialSCC edgesInH
    then do
      lEqOne <- mkEq lvar =<< mkRational (1 :: Prob)
      uEqOne <- mkEq uvar =<< mkRational (1 :: Prob)
      return [lEqOne, uEqOne]
    else do
      transitions <- mapM shiftEnc edgesInH
      lEq <- mkGe lvar =<< mkAdd (map fst transitions)
      uEq <- mkLe uvar =<< mkAdd (map snd transitions)
      soundness <- mkLe lvar uvar
      -- debugging
      eqLString <- astToString lEq
      logInfoN $ "Asserting Shift equation (lower bound): " ++ eqLString
      eqUString <- astToString uEq
      logInfoN $ "Asserting Shift equation (upper bound): " ++ eqUString
      return [lEq, uEq, soundness]
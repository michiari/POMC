{- |
   Module      : Pomc.Satisfiability
   Copyright   : 2020-2023 Michele Chiari
   License     : MIT
   Maintainer  : Michele Chiari
-}

module Pomc.Satisfiability ( Delta(..)
                           , isEmpty
                           , isEmptyOmega
                           , isSatisfiable
                           , isSatisfiableGen
                           , toInputTrace
                           , showTrace
                           ) where

import Pomc.Prop (Prop(..))
import Pomc.Prec (Prec(..), Alphabet)
import Pomc.Potl (Formula(..))
import Pomc.Check (EncPrecFunc, makeOpa, InitialsComputation(..))
import Pomc.PropConv (APType, PropConv(..), convProps)
import Pomc.State (Input, State(..), showState, showAtom)
import Pomc.Encoding (PropSet, BitEncoding, extractInput, decodeInput)

import Pomc.OmegaEncoding (OmegaEncodedSet, OmegaBitencoding)
import qualified Pomc.OmegaEncoding as OE
import Pomc.SatUtil
import Pomc.SCCAlgorithm

import Pomc.SetMap (SetMap)
import qualified Pomc.SetMap as SM

import Pomc.MapMap (MapMap)
import qualified Pomc.MapMap as MM

import Control.Monad (foldM, forM_)
import Control.Monad.ST (ST)
import qualified Control.Monad.ST as ST
import Data.STRef (STRef)
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Hashable
import qualified Data.Vector as V

import Data.IntMap.Strict(IntMap)

-- global variables in the algorithms
data Globals s state = FGlobals
  { sIdGen :: SIdGen s state
  , visited :: STRef s (SetMap s (Stack state))
  , suppStarts :: STRef s (SetMap s (Stack state))
  , suppEnds :: STRef s (SetMap s (StateId state))
  } | WGlobals
  { sIdGen :: SIdGen s state
  , suppStarts :: STRef s (SetMap s (Stack state))
  , wSuppEnds :: STRef s (MapMap s (StateId state) OmegaEncodedSet) -- we store the formulae satisfied in the support
  , graph :: Graph s state
  }

-- a type for the delta relation, parametric with respect to the type of the state
data Delta state = Delta
  { bitenc :: BitEncoding
  , prec :: EncPrecFunc -- precedence function which replaces the precedence matrix
  , deltaPush :: state -> Input -> [state] -- deltaPush relation
  , deltaShift :: state -> Input -> [state] -- deltaShift relation
  , deltaPop :: state -> state -> [state] -- deltapop relation
  }

-- Begin debugging stuff
data TraceType = Push | Shift | Pop | Summary | Found deriving (Eq, Show)
type TraceId state = [(TraceType, StateId state, Stack state)]
type Trace state = [(TraceType, state, Maybe (Input, state))]

unIdTrace :: TraceId state -> Trace state
unIdTrace trace =
  map (\(moveType, q, g) ->
         (moveType, getState q, fmap (\(b, r) -> (b, getState r)) g)) trace

toInputTrace :: (SatState state) => BitEncoding -> Trace state -> [(state, PropSet)]
toInputTrace be trace = foldr foldInput [] trace
  where foldInput (moveType, q, _) rest
          | moveType == Push || moveType == Shift =
            (q, stateToInput q) : rest
          | moveType == Summary =
            (q, Set.empty) : rest
          | moveType == Found =
            (q, Set.singleton End) : rest
          | otherwise = rest
        stateToInput q =
          (decodeInput be) . (extractInput be) . current . getSatState $ q

showTrace :: (SatState state, Show state, Show a)
          => BitEncoding
          -> PropConv a
          -> Trace state
          -> String
showTrace be pconv trace = concatMap showMove trace
  where showMove (moveType, q, g) =
          show moveType     ++ ":\nRaw State:\n" ++
          show q ++ "\nCheck State:\n" ++
          showState be pconv (getSatState q) ++ "\nStack:\n" ++
          showStack g ++ "\n\n"
        showStack (Just (b, r)) =
          showAtom be pconv b ++ "\n" ++
          show r ++ "\n" ++
          showState be pconv (getSatState r)
        showStack Nothing = "Bottom"
-- End debugging stuff

reach :: (SatState state, Eq state, Hashable state, Show state)
      => (StateId state -> Bool) -- is the state as desired?
      -> (Stack state -> Bool) -- is the stack as desired?
      -> Globals s state -- global variables of the algorithm
      -> Delta state -- delta relation of the opa
      -> StateId state -- current state
      -> Stack state -- current stack symbol
      -> TraceId state
      -> ST s (Bool, TraceId state)
reach isDestState isDestStack globals delta q g trace = do
  previouslyVisited <- SM.member (visited globals) (getId q) g
  if previouslyVisited
    then return (False, [])
    else do
    SM.insert (visited globals) (getId q) g
    let qState = getState q
        precRel = (prec delta) (fst . fromJust $ g) (current . getSatState $ qState)
        cases
          | (isDestState q) && (isDestStack g) = return (True, (Found, q, g) : trace)

          | (isNothing g) || precRel == Just Yield =
            reachPush isDestState isDestStack globals delta q g qState trace

          | precRel == Just Equal =
            reachShift isDestState isDestStack globals delta q g qState trace

          | precRel == Just Take =
            reachPop isDestState isDestStack globals delta q g qState trace

          | otherwise = return (False, [])
    cases


reachPush :: (SatState state, Eq state, Hashable state, Show state)
          => (StateId state -> Bool)
          -> (Stack state -> Bool)
          -> Globals s state
          -> Delta state
          -> StateId state
          -> Stack state
          -> state
          -> TraceId  state
          -> ST s (Bool, TraceId state)
reachPush isDestState isDestStack globals delta q g qState trace =
  let qProps = getStateProps (bitenc delta) qState
      doPush res@(True, _) _ = return res
      doPush (False, _) p = reach isDestState isDestStack globals delta p (Just (qProps, q)) ((Push, q, g) : trace)
  in do
    SM.insert (suppStarts globals) (getId q) g
    newStates <- wrapStates (sIdGen globals) $ (deltaPush delta) qState qProps
    res@(pushReached, _) <- V.foldM' doPush (False, []) newStates
    if pushReached
      then return res
      else do
      currentSuppEnds <- SM.lookup (suppEnds globals) (getId q)
      foldM (\acc s -> if fst acc
                       then return acc
                       else reach isDestState isDestStack globals delta s g ((Summary, q, g) : trace))
        (False, [])
        currentSuppEnds


reachShift :: (SatState state, Eq state, Hashable state, Show state)
           => (StateId state -> Bool)
           -> (Stack state -> Bool)
           -> Globals s state
           -> Delta state
           -> StateId state
           -> Stack state
           -> state
           -> TraceId state
           -> ST s (Bool, TraceId state)
reachShift isDestState isDestStack globals delta q g qState trace =
  let qProps = getStateProps (bitenc delta) qState
      doShift res@(True, _) _ = return res
      doShift (False, _) p =
        reach isDestState isDestStack globals delta p (Just (qProps, (snd . fromJust $ g))) ((Shift, q, g) : trace)
  in do
    newStates <- wrapStates (sIdGen globals) $ (deltaShift delta) qState qProps
    V.foldM' doShift (False, []) newStates


reachPop :: (SatState state, Eq state, Hashable state, Show state)
         => (StateId state -> Bool)
         -> (Stack state -> Bool)
         -> Globals s state
         -> Delta state
         -> StateId state
         -> Stack state
         -> state
         -> TraceId state
         -> ST s (Bool, TraceId state)
reachPop isDestState isDestStack globals delta q g qState trace =
  let doPop res@(True, _) _ = return res
      doPop (False, _) p =
        let r = snd . fromJust $ g
            closeSupports res@(True, _) _ = return res
            closeSupports (False, _) g' =
              reach isDestState isDestStack globals delta p g' ((Pop, q, g) : trace)
        in do
          SM.insert (suppEnds globals) (getId r) p
          currentSuppStarts <- SM.lookup (suppStarts globals) (getId r)
          foldM closeSupports (False, []) currentSuppStarts

  in do
    newStates <- wrapStates (sIdGen globals) $
                 (deltaPop delta) qState (getState . snd . fromJust $ g)
    V.foldM' doPop (False, []) newStates

-- check the emptiness of the Language expressed by an automaton
isEmpty :: (SatState state, Eq state, Hashable state, Show state)
        => Delta state -- delta relation of the opa
        -> [state] -- list of initial states of the opa
        -> (state -> Bool) -- determine whether a state is final
        -> (Bool, Trace state)
isEmpty delta initials isFinal =
  let (accepting, trace) = ST.runST $ do
        newSig <- initSIdGen
        emptyVisited <- SM.empty
        emptySuppStarts <- SM.empty
        emptySuppEnds <- SM.empty
        let globals = FGlobals { sIdGen = newSig
                              , visited = emptyVisited
                              , suppStarts = emptySuppStarts
                              , suppEnds = emptySuppEnds
                              }
        initialsId <- wrapStates newSig initials
        foldM (\acc q -> if fst acc
                         then return acc
                         else reach (isFinal . getState) isNothing globals delta q Nothing [])
          (False, [])
          initialsId
  in (not accepting, unIdTrace $ reverse trace)


-- The omega case does not print counterexamples at the moment
------------------------------------------------------------------------------------------
isEmptyOmega  :: (SatState state, Ord state, Hashable state, Show state)
        => Delta state -- delta relation of an opa
        -> [state] -- list of initial states of the opba
        -> OmegaBitencoding state -- a wrapper for some utilities to determine whether a cycle is accepting or not
        -> (Bool, Trace state)
isEmptyOmega delta initialOpbaStates obitenc = (not $
  ST.runST (do
               newSig <- initSIdGen -- a variable to keep track of state to id relation
               emptySuppStarts <- SM.empty
               emptySuppEnds <- MM.empty
               initialsId <- wrapStates newSig initialOpbaStates
               initials <- V.mapM (\sId -> return (sId, Nothing)) initialsId
               gr <- newGraph initials obitenc
               let globals = WGlobals { sIdGen = newSig
                                      , suppStarts = emptySuppStarts
                                      , wSuppEnds = emptySuppEnds
                                      , graph = gr
                                      }
                in searchPhase globals delta
            ), [])

searchPhase :: (SatState state, Ord state, Hashable state, Show state)
                  => Globals s state
                  -> Delta state
                  -> ST.ST s Bool
searchPhase globals delta  =
  let visit (semiconf, mPathSatSet) = do
        mustExplore <- updateSccInitialWith (graph globals) semiconf mPathSatSet
        case mustExplore of
          Explore ss -> reachOmega globals delta semiconf ss
          AlreadyContracted -> return False
          _ -> error "unsupport command for initial states"
  in do
    initials <- initialNodes $ graph globals
    detected <- foldM (\acc ini -> if acc
                                    then return True
                                    else visit ini)
                      False
                      initials
    if detected
      then return True
      else do
        mustCollapse <- toCollapsePhase (graph globals)
        collapsePhase mustCollapse (map fst initials) globals delta

collapsePhase :: (SatState state, Ord state, Hashable state, Show state)
                  => (Bool, IntMap OmegaEncodedSet)
                  -> [(StateId state, Stack state)]
                  -> Globals s state
                  -> Delta state
                  -> ST.ST s Bool
collapsePhase (False,_) _ _ _ = return False
collapsePhase (_, newInitials) initials globals delta =
  let visit = updateSccInitial (graph globals)
  in do
    detected <- foldM (\acc node -> if acc
                                        then return True
                                        else visit node)
                      False
                      initials
    if detected
      then return True
      else do
        toSearchPhase (graph globals) newInitials
        searchPhase globals delta

reachOmega :: (SatState state, Ord state, Hashable state, Show state)
               => Globals s state
               -> Delta state
               -> (StateId state, Stack state)
               -> OmegaEncodedSet
               -> ST.ST s Bool
reachOmega globals delta  (q,g) pathSatSet = do
  let qState = getState q
      precRel = (prec delta) (fst . fromJust $ g) (current . getSatState $ qState)
      cases
        | (isNothing g) || precRel == Just Yield =
          reachOmegaPush globals delta (q,g) qState pathSatSet

        | precRel == Just Equal =
          reachOmegaShift globals delta (q,g) qState pathSatSet

        | precRel == Just Take =
          reachOmegaPop globals delta (q,g) qState pathSatSet

        | otherwise = error "unexpected prec relation"
  success <- cases
  createComponentGn (graph globals) (q,g)
  return success

reachOmegaPush :: (SatState state, Ord state, Hashable state, Show state)
          => Globals s state
          -> Delta state
          -> (StateId state, Stack state)
          -> state
          -> OmegaEncodedSet
          -> ST s Bool
reachOmegaPush globals delta (q,g) qState pathSatSet =
  let qProps = getStateProps (bitenc delta) qState
      doPush True _ = return True
      doPush False p = reachTransition globals delta (p,Just (qProps, q)) Nothing Nothing
  in do
    SM.insert (suppStarts globals) (getId q) g
    newStates <- wrapStates (sIdGen globals) $ (deltaPush delta) qState qProps
    pushReached <- V.foldM' doPush False newStates
    if pushReached
      then return True
      else do
      currentSuppEnds <- MM.lookup (wSuppEnds globals) (getId q)
      foldM (\acc (s, supportSatSet)  -> if acc
                                            then return True
                                            else reachTransition globals delta (s,g) (Just pathSatSet) (Just supportSatSet))
        False
        currentSuppEnds

reachOmegaShift :: (SatState state, Ord state, Hashable state, Show state)
           => Globals s state
           -> Delta state
           -> (StateId state, Stack state)
           -> state
           -> OmegaEncodedSet
           -> ST s Bool
reachOmegaShift globals delta (_,g) qState pathSatSet =
  let qProps = getStateProps (bitenc delta) qState
      doShift True _ = return True
      doShift False p =
        reachTransition globals delta (p, Just (qProps, (snd . fromJust $ g))) (Just pathSatSet) Nothing
  in do
    newStates <- wrapStates (sIdGen globals) $ (deltaShift delta) qState qProps
    V.foldM' doShift False newStates

reachOmegaPop :: (SatState state, Ord state, Hashable state, Show state)
         => Globals s state
         -> Delta state
         -> (StateId state, Stack state)
         -> state
         -> OmegaEncodedSet
         -> ST s Bool
reachOmegaPop globals delta (_,g) qState pathSatSet =
  let doPop p =
        let r = snd . fromJust $ g
            closeSupports g' = insertSummary (graph globals) (r,g') (p,g') pathSatSet
        in do
          MM.insertWith (wSuppEnds globals) (getId r) OE.union p pathSatSet
          currentSuppStarts <- SM.lookup (suppStarts globals) (getId r)
          forM_ currentSuppStarts closeSupports
  in do
    newStates <- wrapStates (sIdGen globals) $
                 (deltaPop delta) qState (getState . snd . fromJust $ g)
    forM_  newStates doPop
    return False

reachTransition :: (SatState state, Ord state, Hashable state, Show state)
                 => Globals s state
                 -> Delta state
                 -> (StateId state, Stack state)
                 -> Maybe OmegaEncodedSet -- pathSatSet
                 -> Maybe OmegaEncodedSet -- supportSatSet for edges
                 -> ST s Bool
reachTransition globals delta to_semiconf pathSatSet edgeSatSet =
  let execute (Explore ss) = reachOmega globals delta to_semiconf ss
      execute AlreadyContracted = return False
      execute Success = return True
  in execute =<< updateSCCs (graph globals) to_semiconf pathSatSet edgeSatSet

-------------------------------------------------------------
-- given a formula, build the opa associated with the formula
-- and check the language expressed by the OPA for emptiness
-- (mainly used for testing)
isSatisfiable :: Bool
              -> Formula APType
              -> Alphabet APType
              -> (Bool, [PropSet])
isSatisfiable isOmega phi alphabet =
  let encode True = IsOmega
      encode False = IsFinite
      
      (be, precf, initials, isFinal, dPush, dShift, dPop, cl) =
        makeOpa phi (encode isOmega) alphabet (\_ _ -> True)
      delta = Delta
        { bitenc = be
        , prec = precf
        , deltaPush = (\q _ -> dPush q Nothing)
        , deltaShift = (\q _ -> dShift q Nothing)
        , deltaPop = dPop
        }
      obe = OE.makeOmegaBitEncoding cl (const True) isFinal
      (emptyRes, trace) = if isOmega
                          then isEmptyOmega delta initials obe
                          else isEmpty delta initials (isFinal T)

  in (not emptyRes, map snd $ toInputTrace be trace)

-- parametric with respect the type of the propositions
isSatisfiableGen :: (Ord a)
                 => Bool
                 -> Formula a
                 -> Alphabet a
                 -> (Bool, [Set (Prop a)])
isSatisfiableGen isOmega phi (sls, precf) =
  let (tphi, tprecr, [tsls], pconv) = convProps phi precf [sls]
      (sat, trace) = isSatisfiable isOmega tphi (tsls, tprecr)
  in (sat, map (Set.map (decodeProp pconv)) trace)

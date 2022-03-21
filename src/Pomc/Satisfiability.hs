{- |
   Module      : Pomc.Satisfiability
   Copyright   : 2020-2021 Michele Chiari
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
import Pomc.Check (EncPrecFunc, makeOpa)
import Pomc.PropConv (APType, PropConv(..), convProps)
import Pomc.State(Input, State(..), showState, showAtom)
import Pomc.Encoding (PropSet, BitEncoding, extractInput, decodeInput)
import Pomc.SatUtil
import Pomc.SCCAlgorithm
import Pomc.SetMap
import qualified Pomc.SetMap as SM

import Control.Monad (foldM, forM_)
import Control.Monad.ST (ST)
import qualified Control.Monad.ST as ST
import Data.STRef (STRef)
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Hashable
import qualified Data.Vector as V

import Control.DeepSeq(NFData(..))

-- import qualified Debug.Trace as DBG

-- global variables in the algorithms
data Globals s state = FGlobals
  { sIdGen :: SIdGen s state
  , visited :: STRef s (SetMap s (Stack state))
  , suppStarts :: STRef s (SetMap s (Stack state))
  , suppEnds :: STRef s (SetMap s (StateId state))
  } | WGlobals
  { sIdGen :: SIdGen s state
  , suppStarts :: STRef s (SetMap s (Stack state))
  , wSuppEnds :: STRef s (SetMap s (StateId state, SummaryBody))
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

reach :: (NFData state, SatState state, Eq state, Hashable state, Show state)
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


reachPush :: (NFData state, SatState state, Eq state, Hashable state, Show state)
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
      doPush (False, _) p = do
        SM.insert (suppStarts globals) (getId q) g
        reach isDestState isDestStack globals delta p (Just (qProps, q)) ((Push, q, g) : trace)
  in do
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


reachShift :: (NFData state, SatState state, Eq state, Hashable state, Show state)
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


reachPop :: (NFData state, SatState state, Eq state, Hashable state, Show state)
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
            closeSupports (False, _) g'
              | isNothing g' ||
                ((prec delta) (fst . fromJust $ g') (current . getSatState . getState $ r)) == Just Yield
              = reach isDestState isDestStack globals delta p g' ((Pop, q, g) : trace)
              | otherwise = return (False, [])
        in do
          SM.insert (suppEnds globals) (getId r) p
          currentSuppStarts <- SM.lookup (suppStarts globals) (getId r)
          foldM closeSupports (False, []) currentSuppStarts

  in do
    newStates <- wrapStates (sIdGen globals) $
                 (deltaPop delta) qState (getState . snd . fromJust $ g)
    V.foldM' doPop (False, []) newStates

-- check the emptiness of the Language expressed by an automaton
isEmpty :: (NFData state, SatState state, Eq state, Hashable state, Show state)
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
isEmptyOmega  :: (NFData state, SatState state, Ord state, Hashable state, Show state)
        => Delta state -- delta relation of an opa
        -> [state] -- list of initial states of the opba
        -> ([state] -> Bool) -- determine whether a list of states determine an accepting computation
        -> (Bool, Trace state)
isEmptyOmega delta initialOpbaStates areFinal = (not $
  ST.runST (do
               newSig <- initSIdGen -- a variable to keep track of state to id relation
               emptySuppStarts <- SM.empty
               emptySuppEnds <- SM.empty
               initialsId <- wrapStates newSig initialOpbaStates
               initials <- V.mapM (\sId -> return (sId, Nothing)) initialsId
               gr <- newGraph initials
               let globals = WGlobals { sIdGen = newSig
                                      , suppStarts = emptySuppStarts
                                      , wSuppEnds = emptySuppEnds
                                      , graph = gr
                                      }
                in searchPhase areFinal globals delta
            ), [])

searchPhase :: (NFData state, SatState state, Ord state, Hashable state, Show state)
                  => ([state] -> Bool)
                  -> Globals s state
                  -> Delta state
                  -> ST.ST s Bool
searchPhase areFinal globals delta  =
  let visit node = do
        alrDisc <- alreadyDiscovered (graph globals) node
        if not alrDisc
          then reachOmega areFinal globals delta Nothing node
          else return False
  in do
    initials <- initialNodes $ graph globals
    detected <- foldM (\acc node -> if acc
                                      then return True
                                      else visit node)
                      False
                      initials
    if detected
      then return True
      else do
        nullSumm <- nullSummaries $ graph globals
        collapsePhase nullSumm initials areFinal globals delta


collapsePhase :: (NFData state, SatState state, Ord state, Hashable state, Show state)
                  => Bool
                  -> Set (StateId state, Stack state)
                  -> ([state] -> Bool)
                  -> Globals s state
                  -> Delta state
                  -> ST.ST s Bool
collapsePhase True _ _ _ _ = return False
collapsePhase _ initials areFinal globals delta =
  let visit node = do
        alrVis <- alreadyVisited (graph globals) node
        if not alrVis
          then visitGraphFromKey (graph globals) areFinal Nothing node
          else return False
  in do
    newInitials <- toCollapsePhase $ graph globals
    detected <- foldM (\acc node -> if acc
                                        then return True
                                        else visit node)
                      False
                      initials
    if detected
      then return True
      else do
        toSearchPhase (graph globals) (newInitials);
        searchPhase areFinal globals delta

reachOmega :: (NFData state, SatState state, Ord state, Hashable state, Show state)
               => ([state] -> Bool)
               -> Globals s state
               -> Delta state
               -> Maybe Edge
               -> (StateId state, Stack state)
               -> ST.ST s Bool
reachOmega areFinal globals delta me (q,g) = do
  let be = bitenc delta
      qProps = getSidProps be q -- atomic propositions holding in the state (the input)
      qState = getState q
      cases 
        | (isNothing g) || ((prec delta) (fst . fromJust $ g) qProps == Just Yield) =
          reachOmegaPush areFinal globals delta (q,g) qState qProps

        | ((prec delta) (fst . fromJust $ g) qProps == Just Equal) =
          reachOmegaShift areFinal globals delta (q,g) qState qProps

        | ((prec delta) (fst . fromJust $ g) qProps == Just Take) =
          reachOmegaPop globals delta (q,g) qState

        | otherwise = return False
  visitNode (graph globals) me (q,g);
  success <- cases
  if success
    then return True
    else createComponent (graph globals) (q,g) areFinal


reachOmegaPush :: (NFData state, SatState state, Ord state, Hashable state, Show state)
          => ([state] -> Bool)
          -> Globals s state
          -> Delta state
          -> (StateId state, Stack state)
          -> state
          -> Input
          -> ST s Bool
reachOmegaPush areFinal globals delta (q,g) qState qProps =
  let doPush True _ = return True
      doPush False p = do
        SM.insert (suppStarts globals) (getId q) g
        reachTransition Nothing areFinal globals delta (q,g) (p,Just (getSidProps (bitenc delta) q, q))
  in do
    newStates <- wrapStates (sIdGen globals) $ (deltaPush delta) qState qProps
    pushReached <- V.foldM' doPush False newStates
    if pushReached
      then return True
      else do
      currentSuppEnds <- SM.lookup (wSuppEnds globals) (getId q)
      foldM (\acc (s, sb)  -> if acc
                              then return True
                              else reachTransition (Just sb) areFinal globals delta (q,g) (s,g))
        False
        currentSuppEnds


reachOmegaShift :: (NFData state, SatState state, Ord state, Hashable state, Show state)
           => ( [state] -> Bool)
           -> Globals s state
           -> Delta state
           -> (StateId state, Stack state)
           -> state
           -> Input
           -> ST s Bool
reachOmegaShift areFinal globals delta (q,g) qState qProps =
  let doShift True _ = return True
      doShift False p =
        reachTransition Nothing areFinal globals delta (q,g) (p, Just (qProps, (snd . fromJust $ g)))
  in do
    newStates <- wrapStates (sIdGen globals) $ (deltaShift delta) qState qProps
    V.foldM' doShift False newStates

reachOmegaPop :: (NFData state, SatState state, Ord state, Hashable state, Show state)
         => Globals s state
         -> Delta state
         -> (StateId state, Stack state)
         -> state
         -> ST s Bool
reachOmegaPop globals delta (_,g) qState =
  let doPop p =
        let r = snd . fromJust $ g
            closeSupports sb g'
              | isNothing g' ||
                ((prec delta) (fst . fromJust $ g') (getSidProps (bitenc delta) r)) == Just Yield
              = discoverSummary (graph globals) (r,g') sb (p,g')
              | otherwise = return ()
        in do
          sb <- discoverSummaryBody (graph globals) r
          SM.insert (wSuppEnds globals) (getId r) (p,sb)
          currentSuppStarts <- SM.lookup (suppStarts globals) (getId r)
          forM_ currentSuppStarts $ closeSupports sb
  in do
    newStates <- wrapStates (sIdGen globals) $
                 (deltaPop delta) qState (getState . snd . fromJust $ g)
    forM_  newStates doPop
    return False


reachTransition :: (NFData state, SatState state, Ord state, Hashable state, Show state)
                 => Maybe SummaryBody
                 -> ([state] -> Bool)
                 -> Globals s state
                 -> Delta state
                 -> (StateId state, Stack state)
                 -> (StateId state, Stack state)
                 -> ST s Bool
reachTransition sb areFinal globals delta from to = do
  alrDisc <- alreadyDiscovered (graph globals) to
  e <- insertEdge (graph globals) from to sb
  if alrDisc
    then do
      alrVis <- alreadyVisited (graph globals) to
      if alrVis
        then do updateSCC (graph globals) to;
                return False
        else visitGraphFromKey (graph globals) areFinal (Just e) to
    else reachOmega areFinal globals delta (Just e) to

-------------------------------------------------------------
-- given a formula, build the opa associated with the formula
-- and check the language expressed by the OPA for emptiness
-- (mainly used for testing)
isSatisfiable :: Bool
              -> Formula APType
              -> Alphabet APType
              -> (Bool, [PropSet])
isSatisfiable isOmega phi alphabet =
  let (be, precf, initials, isFinal, dPush, dShift, dPop, cl) = makeOpa phi isOmega alphabet
      delta = Delta
        { bitenc = be
        , prec = precf
        , deltaPush = (\q _ -> dPush q Nothing)
        , deltaShift = (\q _ -> dShift q Nothing)
        , deltaPop = dPop
        }
      isFinalOmega states = all (\f -> any (isFinal f) states) cl
      (emptyRes, trace) = if isOmega
                          then isEmptyOmega delta initials isFinalOmega
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

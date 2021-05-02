{- |
   Module      : Pomc.Satisfiability
   Copyright   : 2020 Michele Chiari
   License     : MIT
   Maintainer  : Michele Chiari
-}

module Pomc.Satisfiability ( Delta(..)
                           , isEmpty
                           , isEmptyOmega
                           , isSatisfiable
                           , isSatisfiableGen
                           ) where

import Pomc.Prop (Prop(..))
import Pomc.Prec (Prec(..), StructPrecRel)
import Pomc.PotlV2(Formula(..))
import Pomc.Check ( EncPrecFunc, makeOpa)
import Pomc.State(Input, State(..), showState)
import Pomc.PropConv (APType, convPropLabels)
import Pomc.Data (BitEncoding, extractInput)
import Pomc.SatUtil
import Pomc.SCCAlgorithm
import Pomc.SetMap
import qualified Pomc.SetMap as SM



import Control.Monad (foldM, forM_)
import Control.Monad.ST (ST)
import qualified Control.Monad.ST as ST
import Data.STRef (STRef, newSTRef, readSTRef, writeSTRef, modifySTRef')
import Data.Maybe

import Data.Set (Set)
import qualified Data.Set as Set

import Data.Hashable
import qualified Data.HashTable.ST.Basic as BH
import qualified Data.HashTable.Class as H

import qualified Data.Vector.Mutable as MV
import Data.Vector (Vector)
import qualified Data.Vector as V


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

-- implementation of the reachability algorithm, as described in the notes
reach :: (SatState state, Eq state, Hashable state, Show state)
      => (StateId state -> Bool) -- is the state as desired?
      -> (Stack state-> Bool) -- is the stack as desired?
      -> Globals s state -- global variables of the algorithm
      -> Delta state -- delta relation of the opa
      -> StateId state -- current state
      -> Stack state -- stack symbol
      -> ST s Bool
reach isDestState isDestStack globals delta q g = do
  alreadyVisited <- SM.member (visited globals) q g
  if alreadyVisited
    then return False 
    else do
    debug ("Visiting: " ++ show q ++ "\ng = " ++ show g ++ "\n\n\n" ) $ SM.insert (visited globals) q g 
    let be = bitenc delta
        qProps = getSidProps be q -- atomic propositions holding in the state (the input)
        qState = getState q 
        cases
          | (isDestState q) && (isDestStack g) =
            debug ("End: q = " ++ show q ++ "\ng = " ++ show g ++ "\n\n\n") $ return True

          | (isNothing g) || ((prec delta) (fst . fromJust $ g) qProps == Just Yield) =
            reachPush isDestState isDestStack globals delta q g qState qProps

          | ((prec delta) (fst . fromJust $ g) qProps == Just Equal) =
            reachShift isDestState isDestStack globals delta q g qState qProps

          | ((prec delta) (fst . fromJust $ g) qProps == Just Take) =
            reachPop isDestState isDestStack globals delta q g qState

          | otherwise = return False
    cases


reachPush :: (SatState state, Eq state, Hashable state, Show state)
          => (StateId state -> Bool)
          -> (Stack state -> Bool)
          -> Globals s state
          -> Delta state
          -> StateId state
          -> Stack state
          -> state
          -> Input
          -> ST s Bool
reachPush isDestState isDestStack globals delta q g qState qProps =
  let doPush True _ = return True
      doPush False p = do
        SM.insert (suppStarts globals) q g
        debug ("Push: q = " ++ show q ++ "\ng = " ++ show g ++ "\n") $
          reach isDestState isDestStack globals delta p (Just (getSidProps (bitenc delta) q, q))
  in do
    newStates <- wrapStates (sIdGen globals) $ (deltaPush delta) qState qProps
    pushReached <- V.foldM' doPush False newStates
    if pushReached
      then return True
      else do
      currentSuppEnds <- SM.lookup (suppEnds globals) q
      foldM (\acc s -> if acc
                       then return True
                       else debug ("Push (summary): q = " ++ show q
                                   ++ "\ng = " ++ show g
                                   ++ "\ns = " ++ show s) $
                            reach isDestState isDestStack globals delta s g)
        False
        currentSuppEnds


reachShift :: (SatState state, Eq state, Hashable state, Show state)
           => (StateId state -> Bool)
           -> (Stack state -> Bool)
           -> Globals s state
           -> Delta state
           -> StateId state
           -> Stack state
           -> state
           -> Input
           -> ST s Bool
reachShift isDestState isDestStack globals delta q g qState qProps =
  let doShift True _ = return True
      doShift False p =
        debug ("Shift: q = " ++ show q ++ "\ng = " ++ show g ++ "\n") $
        reach isDestState isDestStack globals delta p (Just (qProps, (snd . fromJust $ g)))
  in do
    newStates <- wrapStates (sIdGen globals) $ (deltaShift delta) qState qProps
    V.foldM' doShift False newStates


reachPop :: (SatState state, Eq state, Hashable state, Show state)
         => (StateId state -> Bool)
         -> (Stack state -> Bool)
         -> Globals s state
         -> Delta state
         -> StateId state
         -> Stack state
         -> state
         -> ST s Bool
reachPop isDestState isDestStack globals delta q g qState =
  let doPop True _ = return True
      doPop False p =
        let r = snd . fromJust $ g
            closeSupports True _ = return True
            closeSupports False g'
              | isNothing g' ||
                ((prec delta) (fst . fromJust $ g') (getSidProps (bitenc delta) r)) == Just Yield
              = debug ("Pop: q = " ++ show q ++ "\ng = " ++ show g ++ "\n") $
                reach isDestState isDestStack globals delta p g'
              | otherwise = return False
        in do
          SM.insert (suppEnds globals) r p
          currentSuppStarts <- SM.lookup (suppStarts globals) r
          foldM closeSupports False currentSuppStarts
  in do
    newStates <- wrapStates (sIdGen globals) $
                 (deltaPop delta) qState (getState . snd . fromJust $ g)
    V.foldM' doPop False newStates

-- check the emptiness of the Language expressed by an automaton
isEmpty :: (SatState state, Eq state, Hashable state, Show state)
        => Delta state -- delta relation of an opa
        -> [state] -- list of initial states of the opa
        -> (state -> Bool) -- determine whether a state is final
        -> Bool
isEmpty delta initials isFinal = not $
  ST.runST (do
               newSig <- initSIdGen -- a variable to keep track of state to id relation
               emptyVisited <- SM.empty
               emptySuppStarts <- SM.empty
               emptySuppEnds <- SM.empty
               let globals = FGlobals { sIdGen = newSig -- a variable to keep track of state to id realtion
                                     , visited = emptyVisited
                                     , suppStarts = emptySuppStarts
                                     , suppEnds = emptySuppEnds
                                     }
                 in do
                 initialsId <- wrapStates newSig initials
                 foldM (\acc q -> if acc
                                  then return True
                                  else (reach (isFinal . getState) isNothing globals delta q Nothing))
                   False
                   initialsId)


------------------------------------------------------------------------------------------
isEmptyOmega  :: (SatState state, Ord state, Hashable state, Show state)
        => Delta state -- delta relation of an opa
        -> [state] -- list of initial states of the opa
        -> ([state] -> Bool) -- determine whether a list of states determine an accepting computation
        -> Bool 
isEmptyOmega delta initials areFinal = not $
  ST.runST (do
               newSig <- initSIdGen -- a variable to keep track of state to id relation
               emptySuppStarts <- SM.empty
               emptySuppEnds <- SM.empty
               initialsId <- wrapStates newSig initials
               initials <- V.mapM (\sId -> return (sId, Nothing)) initialsId
               gr <- newGraph initials
               let globals = WGlobals { sIdGen = newSig 
                                      , suppStarts = emptySuppStarts
                                      , wSuppEnds = emptySuppEnds 
                                      , graph = gr
                                      }
                in searchPhase areFinal globals delta
            )

searchPhase :: (SatState state, Ord state, Hashable state, Show state) 
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
        size <- summariesSize $ graph globals
        collapsePhase size initials areFinal globals delta
        

collapsePhase :: (SatState state, Ord state, Hashable state, Show state) 
                  => Int 
                  -> Set (StateId state, Stack state)
                  -> ([state] -> Bool)
                  -> Globals s state 
                  -> Delta state 
                  -> ST.ST s Bool 
collapsePhase 0 _ _ _ _ = return False
collapsePhase _ initials areFinal globals delta = 
  let visit node = do 
        alrVis <- alreadyVisited (graph globals) node 
        if not alrVis
          then visitGraphFromKey (graph globals) (updateSummaryBodies globals) areFinal Nothing node
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

reachOmega :: (SatState state, Ord state, Hashable state, Show state)
               => ([state] -> Bool) 
               -> Globals s state 
               -> Delta state 
               -> Maybe Edge
               -> (StateId state, Stack state) 
               -> ST.ST s Bool 
reachOmega areFinal globals delta e (q,g) = debug ("newReachOmegawithNode: " ++ show (q,g) ++ "\n" ++ "state: " ++ showState (bitenc delta) (getSatState . getState $ q)) $ do 
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

        | otherwise = debug ("No transition found\n") $ return False
  visitNode (graph globals) e (q,g);
  success <- cases
  if success
    then return True 
    else do 
      result <- createComponent (graph globals) (q,g) areFinal
      updateSummaryBodies globals $ snd result
      return $ fst result



reachOmegaPush :: (SatState state, Ord state, Hashable state, Show state)
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
        SM.insert (suppStarts globals) q g
        debug ( "push: q = " ++ show q ++ "\ng = " ++ show g ++ "\n" ++ "}} --> to: q = " ++ show p ++ "\ng = " ++ show (Just (getSidProps (bitenc delta) q, q)))
          $ reachTransition Nothing areFinal globals delta (q,g) (p,Just (getSidProps (bitenc delta) q, q))
  in do
    newStates <- wrapStates (sIdGen globals) $ (deltaPush delta) qState qProps
    pushReached <- V.foldM' doPush False newStates
    if pushReached
      then return True
      else do
      currentSuppEnds <- SM.lookup (wSuppEnds globals) q
      foldM (\acc (s, sb) -> if acc
                              then return True
                              else debug ("Push (summary): q = " ++ show q
                                   ++ "\ng = " ++ show g
                                   ++ "\ns = " ++ show s) $
                                  reachTransition (Just sb) areFinal globals delta (q,g) (s,g))
        False
        currentSuppEnds


reachOmegaShift :: (SatState state, Ord state, Hashable state, Show state)
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
        debug ("Shift: q = " ++ show q ++ "\ng = " ++ show g ++ "\n--> to: " ++ show p ++ "\ng = " ++ show (Just (qProps, (snd . fromJust $ g))) ++ "\n")
          $ reachTransition Nothing areFinal globals delta (q,g) (p, Just (qProps, (snd . fromJust $ g)))
  in do
    newStates <- wrapStates (sIdGen globals) $ (deltaShift delta) qState qProps
    V.foldM' doShift False newStates

reachOmegaPop :: (SatState state, Ord state, Hashable state, Show state)
         => Globals s state
         -> Delta state
         -> (StateId state, Stack state)
         -> state
         -> ST s Bool
reachOmegaPop globals delta (q,g) qState =
  let doPop p =
        let r = snd . fromJust $ g
            closeSupports sb g'
              | isNothing g' ||
                ((prec delta) (fst . fromJust $ g') (getSidProps (bitenc delta) r)) == Just Yield
              = debug  ("Pop: q = " ++ show q ++ "\ng = " ++ show g ++ "\n--> to: q = " ++ show p ++ "\ng = " ++ show g'
                        ++ "\nDiscovered Summary: from q = " ++ show r ++ "\ng = " ++ show g' ++ "\n-----> to: q = " ++ show p ++ "\ng = " ++ show g' ++ "\n\n") 
                $ discoverSummary (graph globals) (r,g') sb (p,g') -- do not explore this node, but store for later exploration, to ensure correctness of the Gabow algo                        
              | otherwise = return ()
        in do
          sb <- discoverSummaryBody (graph globals) r
          SM.insert (wSuppEnds globals) r (p,sb)
          currentSuppStarts <- SM.lookup (suppStarts globals) r
          forM_ currentSuppStarts (closeSupports sb)
  in do
    newStates <- wrapStates (sIdGen globals) $
                 (deltaPop delta) qState (getState . snd . fromJust $ g)
    forM_  newStates doPop
    return False


reachTransition :: (SatState state, Ord state, Hashable state, Show state)
                 => Maybe SummaryBody
                 -> ([state] -> Bool)
                 -> Globals s state
                 -> Delta state
                 -> (StateId state, Stack state)
                 -> (StateId state, Stack state)
                 -> ST s Bool
reachTransition body areFinal globals delta from to = 
  let insert False =  insertInternal (graph globals) from to
      insert True  =  insertSummary (graph globals) from to $ fromJust body
  in do 
    alrDisc <- alreadyDiscovered (graph globals) to
    e <- insert $ isJust body 
    if alrDisc 
      then do 
        alrVis <- alreadyVisited (graph globals) to
        if alrVis 
          then do updateSCC (graph globals) to;
                  debug ("AlreadyVisitedNode: " ++ show to ++ "\n") $ return False 
          else debug ("AlreadyDisc but not alreadyVisitedNode: " ++ show to ++ "\n")
             $ visitGraphFromKey (graph globals) (updateSummaryBodies globals) areFinal (Just e) to
      else reachOmega areFinal globals delta (Just e) to

updateSummaryBodies :: Globals s state -> Maybe (Int,Set Int) -> ST.ST s ()
updateSummaryBodies _ Nothing = return  ()
updateSummaryBodies globals (Just (newId,oldIds)) = SM.modifyAll (wSuppEnds globals) $ \(sid, sb) -> (sid, updateSummaryBody newId oldIds sb)

-------------------------------------------------------------
-- given a formula, build the fopa associated with the formula and check the emptiness of the language expressed by the OPA (mainly used for testing)
isSatisfiable :: Bool
              -> Formula APType
              -> ([Prop APType], [Prop APType])
              -> [StructPrecRel APType]
              -> Bool
isSatisfiable isOmega phi ap sprs =
  let (be, precf, initials, isFinal, dPush, dShift, dPop, cl) = makeOpa phi isOmega ap sprs
      delta = Delta
        { bitenc = be
        , prec = precf
        , deltaPush = dPush
        , deltaShift = dShift
        , deltaPop = dPop
        }
      isFinalOmega states = all (\f -> any (isFinal f) states) $ Set.toList cl
  in if isOmega 
        then not $ isEmptyOmega delta initials isFinalOmega
        else not $ isEmpty delta initials (isFinal T)


-- parametric with respect the type of the propositions
isSatisfiableGen :: ( Ord a)
                 => Bool 
                 -> Formula a
                 -> ([Prop a], [Prop a])
                 -> [StructPrecRel a]
                 -> Bool
isSatisfiableGen isOmega phi ap precf =
  let (tphi, tap, tprecr) = convPropLabels phi ap precf
  in isSatisfiable isOmega tphi tap tprecr
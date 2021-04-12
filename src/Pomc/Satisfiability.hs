{- |
   Module      : Pomc.Satisfiability
   Copyright   : 2020 Michele Chiari
   License     : MIT
   Maintainer  : Michele Chiari
-}

module Pomc.Satisfiability ( isEmpty
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
import Pomc.SatUtils
import Pomc.SCCAlgorithm


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
  , visited :: STRef s (SetMap s (Stack state)) -- already visited states
  , suppStarts :: STRef s (SetMap s (Stack state))
  , suppEnds :: STRef s (SetMap s (StateId state))
  } | WGlobals 
  { sIdGen :: SIdGen s state
  , suppStarts :: STRef s (SetMap s (Stack state))
  , wSuppEnds :: STRef s (SetMap s (StateId state, SummaryBody)) -- TODO: find a way to avoid exposing SummaryBody here
  , graph :: Graph s state 
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
  alreadyVisited <- memberSM (visited globals) q g
  if alreadyVisited
    then return False 
    else do
    debug ("Visiting: " ++ show q ++ "\ng = " ++ show g ++ "\n\n\n" ) $ insertSM (visited globals) q g 
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
        insertSM (suppStarts globals) q g
        debug ("Push: q = " ++ show q ++ "\ng = " ++ show g ++ "\n") $
          reach isDestState isDestStack globals delta p (Just (getSidProps (bitenc delta) q, q))
  in do
    newStates <- wrapStates (sIdGen globals) $ (deltaPush delta) qState qProps
    pushReached <- V.foldM' doPush False newStates
    if pushReached
      then return True
      else do
      currentSuppEnds <- lookupSM (suppEnds globals) q
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
          insertSM (suppEnds globals) r p
          currentSuppStarts <- lookupSM (suppStarts globals) r
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
               emptyVisited <- emptySM
               emptySuppStarts <- emptySM
               emptySuppEnds <- emptySM
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
        -> Bool -- TODO: implement this
isEmptyOmega delta initials areFinal = not $
  ST.runST (do
               newSig <- initSIdGen -- a variable to keep track of state to id relation
               emptySuppStarts <- emptySM
               emptySuppEnds <- emptySM
               initialsId <- wrapStates newSig initials
               initialNodes <- V.mapM (\sId -> return (sId, Nothing)) initialsId
               gr <- newGraph initialNodes
               let globals = WGlobals { sIdGen = newSig 
                                      , suppStarts = emptySuppStarts
                                      , wSuppEnds = emptySuppEnds 
                                      , graph = gr
                                      }
                in visitInitials areFinal globals delta
            )

-- TODO: make more readable this code
visitInitials :: (SatState state, Ord state, Hashable state, Show state) 
                  => ([state] -> Bool)
                  -> Globals s state 
                  -> Delta state 
                  -> ST.ST s Bool
visitInitials areFinal globals delta  = let 
                                            updateSbs Nothing = return ()
                                            updateSbs (Just(newId, oldIds)) = modifyAllSM (wSuppEnds globals) $ \(sid, sb) -> (sid, updateSummaryBody newId oldIds sb)
                                            visit node = do
                                                            alrDisc <- alreadyDiscovered (graph globals) node 
                                                            if not alrDisc
                                                              then reachOmega areFinal globals delta node
                                                              else return False
                                            autoVisit node = do 
                                                                alrVis <- alreadyVisited (graph globals) node 
                                                                if not alrVis
                                                                  then visitGraphFrom (graph globals) updateSbs areFinal node 
                                                                  else return False

                                        in do 
                                          initials <- initialNodes (bitenc delta) $ graph globals
                                          detected <- foldM (\acc node -> if acc
                                                                            then return True
                                                                            else visit node ) 
                                                            False
                                                            initials
                                          if detected 
                                            then return True 
                                            else do size <- summariesSize $ graph globals
                                                    if size > 0
                                                      then do
                                                          newInitials <- debug ("Moving to collapse phase") $ toCollapsePhase $ graph globals
                                                          autoDetected <- foldM (\acc node -> if acc
                                                                                                then return True
                                                                                                else autoVisit node) 
                                                                                False
                                                                                initials
                                                          if autoDetected 
                                                            then return True 
                                                            else do 
                                                              debug ("Moving to search phase again...") $ toSearchPhase (graph globals) (newInitials);
                                                              visitInitials areFinal globals delta
                                                      else return False  


reachOmega :: (SatState state, Ord state, Hashable state, Show state)
               => ([state] -> Bool) 
               -> Globals s state 
               -> Delta state 
               -> (StateId state, Stack state) 
               -> ST.ST s Bool 
reachOmega areFinal globals delta (q,g) = debug ("newReachOmegawithNode: " ++ show (q,g) ++ "\n" ++ "state: " ++ showState (bitenc delta) (getSatState . getState $ q)) $ do 
  visitNode (graph globals) (q,g)
  let be = bitenc delta 
      qProps = getSidProps be q -- atomic propositions holding in the state (the input)
      qState = getState q 
      updateSbs Nothing = return ()
      updateSbs (Just(newId, oldIds)) = modifyAllSM (wSuppEnds globals) $ \(sid, sb) -> (sid, updateSummaryBody newId oldIds sb)
      cases 
        | (isNothing g) || ((prec delta) (fst . fromJust $ g) qProps == Just Yield) =
          reachOmegaPush areFinal globals delta (q,g) qState qProps

        | ((prec delta) (fst . fromJust $ g) qProps == Just Equal) =
          reachOmegaShift areFinal globals delta (q,g) qState qProps

        | ((prec delta) (fst . fromJust $ g) qProps == Just Take) =
          reachOmegaPop globals delta (q,g) qState

        | otherwise = debug ("No transition found\n") $ return False
    
  success <- cases
  if success
    then return True 
    else do 
      result <- createComponent (graph globals) (q,g) areFinal
      updateSbs $ snd result
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
        insertSM (suppStarts globals) q g
        debug ""--("Push: q = " ++ show q ++ "\ng = " ++ show g ++ "\n") $
          reachTransition Nothing areFinal globals delta (q,g) (p,Just (getSidProps (bitenc delta) q, q))
  in do
    newStates <- wrapStates (sIdGen globals) $ (deltaPush delta) qState qProps
    pushReached <- V.foldM' doPush False newStates
    if pushReached
      then return True
      else do
      currentSuppEnds <- lookupSM (wSuppEnds globals) q
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
        debug ""--("Shift: q = " ++ show q ++ "\ng = " ++ show g ++ "\n") $
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
              = debug  ("Pop: q = " ++ show q ++ "\ng = " ++ show g ++ "}} --> to: q = " ++ show p ++ "\ng = " ++ show g') 
                $ discoverSummary (graph globals) (r,g') sb (p,g') -- do not explore this node, but store for later exploration, to ensure correctness of the Gabow algo                        
              | otherwise = return ()
        in do
          sb <- discoverSummaryBody (graph globals) r
          insertSM (wSuppEnds globals) r (p,sb)
          currentSuppStarts <- lookupSM (suppStarts globals) r
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
      updateSbs Nothing = return  ()
      updateSbs (Just (newId,oldIds)) = modifyAllSM (wSuppEnds globals) $ \(sid, sb) -> (sid, updateSummaryBody newId oldIds sb)
  in do 
    alrDisc <- alreadyDiscovered (graph globals) to
    insert $ isJust body 
    if alrDisc 
      then do 
        alrVis <- alreadyVisited (graph globals) to
        if alrVis 
          then do updateSCC (graph globals) to;
                  debug ("AlreadyVisitedNode: " ++ show to ++ "\n") $ return False 
          else debug ("AlreadyDisc but not alreadyVisitedNode: " ++ show to ++ "\n") $ visitGraphFrom (graph globals) updateSbs areFinal to
      else reachOmega areFinal globals delta to


 
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
      isFinalOmega states = let isFin f s = debug ("IsFinCheck: f = " ++ show f ++ "; s = " ++ show s ++" -- with result: " ++ show (isFinal f (getSatState s)) ++ "\n" ) $ isFinal f (getSatState s)
                                x = map (\f -> (f,any (\s -> isFin f s) states)) $ Set.toList cl
                                y = filter (\(_,b) -> not b) x 
                            in debug ("Non accepted formulas: " ++ show y) $ null y


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
  in debug ("Input formula: " ++ show tphi ++ "\n\n") $ isSatisfiable isOmega tphi tap tprecr







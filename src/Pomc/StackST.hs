-- | Provides a stack container for use in the 'ST' monad
module Pomc.StackST (
    Stack,
    stackNew,
    stackPush,
    stackPeek,
    stackPop,
    stackIsEmpty,
    stackSize,
  )
  where

import Data.STRef
import Control.Monad.ST
import qualified Data.Stack as Pure
import Numeric.Natural

-- | A mutable stack in state thread s, containing values of type a
newtype Stack s a = Stack (STRef s (Pure.Stack a))

-- | Create new empty Stack
stackNew :: ST s (Stack s a)
stackNew = do
    stackRef <- newSTRef Pure.stackNew
    return (Stack stackRef)

-- | Push item onto Stack
stackPush :: Stack s a -> a -> ST s ()
stackPush (Stack stackRef) item = modifySTRef' stackRef (\stack -> Pure.stackPush stack item)

-- | Pop most recently added item without removing from the Stack
stackPeek :: Stack s a -> ST s (Maybe a)
stackPeek (Stack stackRef) = do
    stack <- readSTRef stackRef
    return (Pure.stackPeek stack)

-- | Pop most recently added item from Stack
stackPop :: Stack s a -> ST s (Maybe a)
stackPop (Stack stackRef) = do
    stack <- readSTRef stackRef
    case Pure.stackPop stack of
      Just (stack1,item) -> do writeSTRef stackRef stack1
                               return (Just item)
      Nothing -> return Nothing

-- | Test if stack is empty
stackIsEmpty :: Stack s a -> ST s Bool
stackIsEmpty (Stack stackRef) = do
    stack <- readSTRef stackRef
    return (Pure.stackIsEmpty stack)

-- | Compute number of elements contained in the Stack
stackSize :: Stack s a -> ST s Natural
stackSize (Stack stackRef) = do
    stack <- readSTRef stackRef
    return (Pure.stackSize stack)
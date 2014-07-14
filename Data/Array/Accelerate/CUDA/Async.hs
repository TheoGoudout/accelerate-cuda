{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE GADTs               #-}

module Data.Array.Accelerate.CUDA.Async (

  -- *
  Async(..), wait, waitSafe, after, afterSafe

  ) where

import Control.Exception                                        ( bracket_ )
import System.IO.Unsafe                                         ( unsafePerformIO )

import Data.Array.Accelerate.CUDA.Context
import Data.Array.Accelerate.CUDA.Execute.Event                 ( Event )
import Data.Array.Accelerate.CUDA.Execute.Stream                ( Stream )
import qualified Data.Array.Accelerate.CUDA.Execute.Event       as Event

-- Asynchronous kernel execution
-- -----------------------------

-- Arrays with an associated CUDA Event that will be signalled once the
-- computation has completed.
--
data Async a where
  Async         :: {-# UNPACK #-} !Event
                -> !a
                -> Context
                -> Async a

after :: Stream -> Async a -> a
after st async = unsafePerformIO $ afterSafe st async

afterSafe :: Stream -> Async a -> IO a
afterSafe st (Async event arr ctx) =
  bracket_ start end action
  where
    start = push ctx
    end   = pop
    --
    action = Event.after event st >> return arr

-- Block the calling thread until the event for the given array computation
-- is recorded.
--
wait :: Async a -> a
wait async = unsafePerformIO $ waitSafe async

waitSafe :: Async a -> IO a
waitSafe (Async event arr ctx) =
  bracket_ start end action
  where
    start = push ctx
    end   = pop
    --
    action = Event.block event >> return arr
{-# LANGUAGE GADTs               #-}

module Data.Array.Accelerate.CUDA.Async (

  -- *
  Async(..), after, wait, streaming

  ) where

import Control.Applicative                                      ( (<$>) )
import Control.Monad.Reader                                     ( asks )
import Control.Monad.State                                      ( gets )
import Control.Monad.Trans                                      ( MonadIO, liftIO )

import Data.Array.Accelerate.CUDA.State                         ( CIO, activeContext, streamReservoir)
import Data.Array.Accelerate.CUDA.Execute.Event                 ( Event )
import Data.Array.Accelerate.CUDA.Execute.Stream                ( Stream )
import qualified Data.Array.Accelerate.CUDA.Execute.Event       as Event
import qualified Data.Array.Accelerate.CUDA.Execute.Stream      as Stream


-- Asynchronous kernel execution
-- -----------------------------

-- Arrays with an associated CUDA Event that will be signalled once the
-- computation has completed.
--
data Async a where
  Async       :: {-# UNPACK #-} !Event
              -> !a
              -> Async a

-- All work submitted to the given stream will occur after the asynchronous
-- event for the given array has been fulfilled. Synchronisation is performed
-- efficiently on the device. This function returns immediately.
--
after :: MonadIO m => Stream -> Async a -> m a
after stream (Async       event arr) = liftIO $ Event.after event stream >> return arr


-- Block the calling thread until the event for the given array computation
-- is recorded.
--
wait :: MonadIO m => Async a -> m a
wait (Async       event arr) = liftIO $ Event.block event >> return arr


-- Execute the given computation in a unique execution stream.
--
streaming :: (Stream -> CIO a) -> CIO (Async a)
streaming action = do
  context   <- asks activeContext
  reservoir <- gets streamReservoir
  --
  uncurry Async <$> Stream.streaming context reservoir action
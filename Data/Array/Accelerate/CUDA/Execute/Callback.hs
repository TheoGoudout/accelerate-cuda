{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE GADTs               #-}

module Data.Array.Accelerate.CUDA.Execute.Callback (

  initialise, performCallbackAsync

) where

import Control.Monad.IO.Class
import Foreign.CUDA.Driver               hiding (initialise, pokeArray)
import Foreign.Marshal.Array

import Data.Array.Accelerate.CUDA.State
import Data.Array.Accelerate.CUDA.Execute.Async

initialise :: CIO (Fun, HostPtr Bool)
initialise = do
  !mdl  <- liftIO $ loadFile "/home/theog/blocking.cubin"
  !fn   <- liftIO $ getFun mdl "blockingKernel"
  --
  !hptr <- liftIO $ mallocHostArray [DeviceMapped] 1
  liftIO $ withHostPtr hptr $ \ptr -> pokeArray ptr [True]
  --
  return (fn,hptr)

performCallbackAsync :: IO () -> Fun -> HostPtr Bool -> CIO (Async ())
performCallbackAsync action !fn !hptr =
  streaming $ \st -> do
    !dptr <- liftIO $ getDevicePtr [] hptr
    --
    liftIO $ putStrLn "addCallback"
    liftIO $ addCallback action' (Just st)
    liftIO $ putStrLn "launchKernel"
    liftIO $ launchKernel fn (1,1,1) (1,1,1) 0 (Just st) [VArg dptr]
  where
    action' _ = do
      putStrLn "Start action"
      action
      putStrLn "unlock kernel"
      withHostPtr hptr $ \ptr -> pokeArray ptr [False]

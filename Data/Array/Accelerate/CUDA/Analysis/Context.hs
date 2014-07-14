{-# LANGUAGE BangPatterns               #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE CPP                        #-}


module Data.Array.Accelerate.CUDA.Analysis.Context (

  -- * 
  choseContextIn, push, pop

) where

import Data.List                                        ( delete )
import Data.IORef                                       ( IORef, newIORef, readIORef, atomicModifyIORef' )
import System.IO.Unsafe                                 ( unsafePerformIO )
import Data.Function                                    ( on )
import Control.Applicative                              ( (<$>) )
import Foreign.CUDA.Driver.Device                       ( name )
import Foreign.CUDA.Driver.Context                      ( device )

-- friends
import Data.Array.Accelerate.CUDA.State                 ( defaultContexts )
import Data.Array.Accelerate.CUDA.Context               hiding ( push, pop )
import Data.Array.Accelerate.CUDA.Analysis
import qualified Data.Array.Accelerate.CUDA.Context     as Ctx

-- | Informations relative to a device.
-- Stocks its context and all the current tasks
-- associated to it.
--
data DeviceInfo a = DeviceInfo {
    context :: Context,
    jobs    :: [AnalysisAcc a]
    }

instance Eq (DeviceInfo a) where
  (==) = (==) `on` context

instance Ord (DeviceInfo a) where
  compare dev dev' = compare (fold $ map analysis (jobs dev)) (fold $ map analysis (jobs dev'))

instance Show (DeviceInfo a) where
  show (DeviceInfo c j) = "DeviceInfo = { " ++
                          (deviceName c) ++ ", " ++
                          (show $ fold (map analysis j)) ++ "}"
    where
      deviceName :: Context -> String
      deviceName ctx = unsafePerformIO $ do
        Ctx.push ctx
        dev <- device
        str <- name dev
        Ctx.pop
        return str


-- | Global contexts state
-- This is a little hack to simulate a global monadic value
-- We want to keep track of current running computations.
--
{-# NOINLINE state #-}
state :: IORef [DeviceInfo a]
state = unsafePerformIO $ newIORef (map lift defaultContexts)

-- | Thread safe
--
get :: IO [DeviceInfo a]
get = readIORef state

-- | Thread safe
--
push :: AnalysisAcc a -> Context -> IO ()
push a !ctx = do
  atomicModifyIORef' state $ \devs -> (map addJob devs,())
  where
    addJob dev =
      if ctx == context dev
        then (DeviceInfo (context dev) (a:jobs dev))
        else dev

-- | Thread safe
--
pop :: AnalysisAcc a -> Context -> IO (AnalysisAcc a)
pop a !ctx = atomicModifyIORef' state $ \devs -> (map delJob devs,a)
  where
    delJob dev =
      if ctx == context dev
        then (DeviceInfo (context dev) (delete a (jobs dev)))
        else dev

-- |
--
lift :: Context -> DeviceInfo a
lift = flip DeviceInfo []


-- | Chose a context for the next computation within a given set of contexts
--
choseContextIn :: [Context] -> IO Context
choseContextIn ctxs = do
  !devs <- filter (\dev -> (context dev) `elem` ctxs) <$> get
  return $ context $ minimum devs

{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- |
-- Module      : Data.Array.Accelerate.CUDA.Array.Registration
-- Copyright   : [2008..2010] Manuel M T Chakravarty, Gabriele Keller, Sean Lee
--               [2009..2014] Manuel M T Chakravarty, Gabriele Keller, Trevor L. McDonell, Theo Goudout
-- License     : BSD3
--
-- Maintainer  : Theo Goudout <tgou051@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.CUDA.Array.Registration (

    -- * 
    register, unregister

) where

import Control.Monad.IO.Class                           ( liftIO )

import Data.Array.Accelerate.Array.Sugar                ( Arrays(..), ArraysR(..) )

import qualified Data.Array.Accelerate.CUDA.Array.Data  as Data

--
--
register :: forall arrs. Arrays arrs => arrs -> IO ()
register !arrs = liftIO $ registerR (arrays (undefined::arrs)) (fromArr arrs)
  where
    registerR :: ArraysR a -> a -> IO ()
    registerR ArraysRunit         ()             = return ()
    registerR ArraysRarray        arr            = Data.registerArray arr
    registerR (ArraysRpair r1 r2) (arrs1, arrs2) = registerR r1 arrs1 >> registerR r2 arrs2

--
--
unregister :: forall arrs. Arrays arrs => arrs -> IO ()
unregister !arrs = unregisterR (arrays (undefined::arrs)) (fromArr arrs)
  where
    unregisterR :: ArraysR a -> a -> IO ()
    unregisterR ArraysRunit         ()             = return ()
    unregisterR ArraysRarray        arr            = Data.unregisterArray arr
    unregisterR (ArraysRpair r1 r2) (arrs1, arrs2) = unregisterR r1 arrs1 >> unregisterR r2 arrs2
{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE CPP                 #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE ScopedTypeVariables #-}
-- |
-- Module      : Data.Array.Accelerate.CUDA
-- Copyright   : [2008..2010] Manuel M T Chakravarty, Gabriele Keller, Sean Lee
--               [2009..2013] Manuel M T Chakravarty, Gabriele Keller, Trevor L. McDonell
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <tmcdonell@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
-- This module implements the CUDA backend for the embedded array language
-- /Accelerate/. Expressions are on-line translated into CUDA code, compiled,
-- and executed in parallel on the GPU.
--
-- The accelerate-cuda library is hosted at: <https://github.com/AccelerateHS/accelerate-cuda>.
-- Comments, bug reports, and patches, are always welcome.
--
--
-- [/Data transfer:/]
--
-- GPUs typically have their own attached memory, which is separate from the
-- computer's main memory. Hence, every 'Data.Array.Accelerate.use' operation
-- implies copying data to the device, and every 'run' operation must copy the
-- results of a computation back to the host.
--
-- Thus, it is best to keep all computations in the 'Acc' meta-language form and
-- only 'run' the computation once at the end, to avoid transferring (unused)
-- intermediate results.
--
-- Note that once an array has been transferred to the GPU, it will remain there
-- for as long as that array remains alive on the host. Any subsequent calls to
-- 'Data.Array.Accelerate.use' will find the array cached on the device and not
-- re-transfer the data.
--
--
-- [/Caching and performance:/]
--
-- When the program runs, the /Accelerate/ library evaluates the expression
-- passed to 'run' to make a series of CUDA kernels. Each kernel takes some
-- arrays as inputs and produces arrays as output. Each kernel is a piece of
-- CUDA code that has to be compiled and loaded onto the GPU; this can take a
-- while, so we remember which kernels we have seen before and try to re-use
-- them.
--
-- The goal is to make kernels that can be re-used. If we don't, the overhead of
-- compiling new kernels can ruin performance.
--
-- For example, consider the following implementation of the function
-- 'Data.Array.Accelerate.drop' for vectors:
--
-- > drop :: Elt e => Exp Int -> Acc (Vector e) -> Acc (Vector e)
-- > drop n arr =
-- >   let n' = the (unit n)
-- >   in  backpermute (ilift1 (subtract n') (shape arr)) (ilift1 (+ n')) arr
--
-- Why did we go to the trouble of converting the @n@ value into a scalar array
-- using 'Data.Array.Accelerate.unit', and then immediately extracting that
-- value using 'Data.Array.Accelerate.the'?
--
-- We can look at the expression /Accelerate/ sees by evaluating the argument to
-- 'run'. Here is what a typical call to 'Data.Array.Accelerate.drop' evaluates
-- to:
--
-- >>> drop (constant 4) (use (fromList (Z:.10) [1..]))
-- let a0 = use (Array (Z :. 10) [1,2,3,4,5,6,7,8,9,10]) in
-- let a1 = unit 4
-- in backpermute
--      (let x0 = Z in x0 :. (indexHead (shape a0)) - (a1!x0))
--      (\x0 -> let x1 = Z in x1 :. (indexHead x0) + (a1!x1))
--      a0
--
-- The important thing to note is the line @let a1 = unit 4@. This corresponds
-- to the scalar array we created for the @n@ argument to
-- 'Data.Array.Accelerate.drop' and it is /outside/ the call to
-- 'Data.Array.Accelerate.backpermute'. The 'Data.Array.Accelerate.backpermute'
-- function is what turns into a CUDA kernel, and to ensure that we get the same
-- kernel each time we need the arguments to it to remain constant.
--
-- Let us see what happens if we change 'Data.Array.Accelerate.drop' to instead
-- use its argument @n@ directly:
--
-- >>> drop (constant 4) (use (fromList (Z:.10) [1..]))
-- let a0 = use (Array (Z :. 10) [1,2,3,4,5,6,7,8,9,10])
-- in backpermute (Z :. -4 + (indexHead (shape a0))) (\x0 -> Z :. 4 + (indexHead x0)) a0
--
-- Instead of @n@ being outside the call to 'Data.Array.Accelerate.backpermute',
-- it is now embedded in it. This will defeat /Accelerate/'s caching of CUDA
-- kernels. Whenever the value of @n@ changes, a new kernel will need to be
-- compiled.
--
-- The rule of thumb is to make sure that any arguments that change are always
-- passed in as arrays, not embedded in the code as constants.
--
-- How can you tell if you got it wrong? One way is to look at the code
-- directly, as in this example. Another is to use the debugging options
-- provided by the library. See debugging options below.
--
--
-- [/Hardware support:/]
--
-- CUDA devices are categorised into different \'compute capabilities\',
-- indicating what operations are supported by the hardware. For example, double
-- precision arithmetic is only supported on devices of compute capability 1.3
-- or higher.
--
-- Devices generally perform best when dealing with (tuples of) 32-bit types, so
-- be cautious when introducing 8-, 16-, or 64-bit elements. Keep in mind the
-- size of 'Int' and 'Data.Word.Word' changes depending on the architecture GHC
-- runs on.
--
-- In particular:
--
--  * 'Double' precision requires compute-1.3.
--
--  * 'Bool' is represented internally using 'Data.Word.Word8', 'Char' by
--    'Data.Word.Word32'.
--
--  * If the permutation function to 'Data.Array.Accelerate.permute' resolves to
--    non-unique indices, the combination function requires compute-1.1 to
--    combine 32-bit types, or compute-1.2 for 64-bit types. Tuple components
--    are resolved separately.
--
--
-- [/Debugging options:/]
--
-- When the library is installed with the @-fdebug@ flag, a few extra debugging
-- options are available, input via the command line arguments. The most useful
-- ones are:
--
--  * @-dverbose:@ Print some information on the type and capabilities of the
--    GPU being used.
--
--  * @-ddump-cc:@ Print information about the CUDA kernels as they are compiled
--    and run. Using this option will indicate whether your program is
--    generating the number of kernels that you were expecting. Note that
--    compiled kernels are cached in your home directory, and the generated code
--    will only be displayed if it was not located in this persistent cache. To
--    clear the cache and always print the generated code, use @-fflush-cache@
--    as well.
--
--  * @-ddump-exec:@ Print each kernel as it is being executed, with timing
--    information.
--
-- See the @accelerate-cuda.cabal@ file for the full list of options.
--
--
-- [/Automatic Graphics Switching on Mac OS X:/]
--
-- Some Apple computers contain two graphics processors: a low-power integrated
-- graphics chipset, as well as a higher-performance NVIDIA GPU. The latter is
-- of course the one we want to use. Usually Mac OS X detects whenever a program
-- attempts to run a CUDA function and switches to the NVIDIA GPU automatically.
--
-- However, sometimes this does not work correctly and the problem can manifest
-- in several ways:
--
--  * The program may report an error such as \"No CUDA-capable device is
--    available\" or \"invalid context handle\".
--
--  * For programs that also use OpenGL, the graphics switching might occur and
--    the Accelerate computation complete as expected, but no OpenGL updates
--    appear on screen.
--
-- There are several solutions:
--
--  * Use a tool such as /gfxCardStatus/ to manually select either the
--    integrated or discrete GPU: <http://gfx.io>
--
--  * Disable automatic graphics switching in the Energy Saver pane of System
--    Preferences. Since this disables use of the low-power integrated GPU, this
--    can decrease battery life.
--
--  * When executing the program, disable the RTS clock by appending @+RTS -V0@
--    to the command line arguments. This disables the RTS clock and all timers
--    that depend on it: the context switch timer and the heap profiling timer.
--    Context switches still happen, but deterministically and at a rate much
--    faster than normal. Automatic graphics switching will work correctly, but
--    this method has the disadvantage of reducing performance of the program.
--

module Data.Array.Accelerate.CUDA (

  Arrays,

  -- * Synchronous execution
  run, run1,  runIn, run1In, stream, streamIn,

  -- * Asynchronous execution
  Async(..), wait, after,
  runAsync, run1Async, runAsyncIn, run1AsyncIn, streamAsync, streamAsyncIn,

  -- * Execution contexts
  Context, create, destroy,
  defaultContexts

) where

-- standard library
import Control.Exception
import Control.Monad.Trans                                 hiding ( lift )
import Control.Monad.Reader                                ( asks )
import System.IO.Unsafe

-- friends
import Data.Array.Accelerate.Trafo                         hiding ( convertAcc )
import Data.Array.Accelerate.Smart                         ( Acc )
import Data.Array.Accelerate.Array.Sugar                   ( Arrays(..), ArraysR(..) )
import Data.Array.Accelerate.CUDA.Analysis
import Data.Array.Accelerate.CUDA.Analysis.Context
import Data.Array.Accelerate.CUDA.Array.Data
import Data.Array.Accelerate.CUDA.Async
import Data.Array.Accelerate.CUDA.Compile
import Data.Array.Accelerate.CUDA.Context                  hiding ( push, pop )
import Data.Array.Accelerate.CUDA.Execute
import Data.Array.Accelerate.CUDA.State
import qualified Data.Array.Accelerate.CUDA.Execute.Async  as Exec

#if ACCELERATE_DEBUG
import Data.Array.Accelerate.Debug
#endif


-- Accelerate: CUDA
-- ----------------

-- | Compile and run a complete embedded array program using the CUDA backend.
-- This will select the fastest device available on which to execute
-- computations, based on compute capability and estimated maximum GFLOPS.
--
-- Note that it is recommended you use 'run1' whenever possible.
--
run :: Arrays a => Acc a -> a
run a
  = unsafePerformIO
  $ evaluate (runIn defaultContexts a)

-- | As 'run', but allow the computation to continue running in a thread and
-- return immediately without waiting for the result. The status of the
-- computation can be queried using 'wait', 'poll', and 'cancel'.
--
-- Note that a CUDA Context can be active on only one host thread at a time. If
-- you want to execute multiple computations in parallel, use 'runAsyncIn'.
--
runAsync :: Arrays a => Acc a -> Async a
runAsync a
  = unsafePerformIO
  $ evaluate (runAsyncIn defaultContexts a)

-- | As 'run', but execute using the specified device context rather than using
-- the default, automatically selected device.
--
-- Contexts passed to this function may all refer to the same device, or to
-- separate devices of differing compute capabilities.
--
-- Note that each thread has a stack of current contexts, and calling
-- 'Foreign.CUDA.Driver.Context.create' pushes the new context on top of the
-- stack and makes it current with the calling thread. You should call
-- 'Foreign.CUDA.Driver.Context.pop' to make the context floating before passing
-- it to 'runIn', which will make it current for the duration of evaluating the
-- expression. See the CUDA C Programming Guide (G.1) for more information.
--
runIn :: Arrays a => [Context] -> Acc a -> a
runIn ctxs a
  = unsafePerformIO
  $ evaluate (runAsyncIn ctxs a) >>= waitSafe


-- | As 'runIn', but execute asynchronously. Be sure not to destroy the context,
-- or attempt to attach it to a different host thread, before all outstanding
-- operations have completed.
--
runAsyncIn :: Arrays a => [Context] -> Acc a -> Async a
runAsyncIn ctxs a = unsafePerformIO $ do
    !ctx   <- choseContextIn ctxs
    !comp  <- evalCUDA ctx (compileAcc acc) >>= dumpStats
    --
    push ana ctx >> evalCUDA ctx (executeAcc comp >>= collectAsync)
  where
    !acc  = convertAccWith config a
    !ana  = analyseAcc acc

-- | Prepare and execute an embedded array program of one argument.
--
-- This function can be used to improve performance in cases where the array
-- program is constant between invocations, because it allows us to bypass all
-- front-end conversion stages and move directly to the execution phase. If you
-- have a computation applied repeatedly to different input data, use this. If
-- the function is only evaluated once, this is equivalent to 'run'.
--
-- To use 'run1' you must express your program as a function of one argument. If
-- your program takes more than one argument, you can use
-- 'Data.Array.Accelerate.lift' and 'Data.Array.Accelerate.unlift' to tuple up
-- the arguments.
--
-- At an example, once your program is expressed as a function of one argument,
-- instead of the usual:
--
-- > step :: Acc (Vector a) -> Acc (Vector b)
-- > step = ...
-- >
-- > simulate :: Vector a -> Vector b
-- > simulate xs = run $ step (use xs)
--
-- Instead write:
--
-- > simulate xs = run1 step xs
--
-- You can use the debugging options to check whether this is working
-- successfully by, for example, observing no output from the @-ddump-cc@ flag
-- at the second and subsequent invocations.
--
-- See the programs in the 'accelerate-examples' package for examples.
--
run1 :: (Arrays a, Arrays b) => (Acc a -> Acc b) -> a -> b
run1 f
  = unsafePerformIO
  $ evaluate (run1In defaultContexts f)


-- | As 'run1', but the computation is executed asynchronously.
--
run1Async :: (Arrays a, Arrays b) => (Acc a -> Acc b) -> a -> Async b
run1Async f
  = unsafePerformIO
  $ evaluate (run1AsyncIn defaultContexts f)

-- | As 'run1', but execute in the specified context.
--
run1In :: (Arrays a, Arrays b) => [Context] -> (Acc a -> Acc b) -> a -> b
run1In !ctxs f = let go = run1AsyncIn ctxs f
               in \a -> unsafePerformIO $ waitSafe (go a)

-- | As 'run1In', but execute asynchronously.
--
run1AsyncIn :: (Arrays a, Arrays b) => [Context] -> (Acc a -> Acc b) -> a -> Async b
run1AsyncIn ctxs f arrs = unsafePerformIO $ do
    !ctx   <- choseContextIn ctxs
    !afun  <- evalCUDA ctx (compileAfun acc) >>= dumpStats
    --
    push ana ctx >> evalCUDA ctx (executeAfun1 afun arrs >>= collectAsync)
  where
    !acc  = convertAfunWith config f
    !ana  = analyseAfun acc arrs


-- TLM: We need to be very careful with run1* variants, to ensure that the
--      returned closure shortcuts directly to the execution phase.


-- | Stream a list of input arrays through the given program,
--   collecting results as we go.
--
stream :: (Arrays a, Arrays b) => (Acc a -> Acc b) -> [a] -> [b]
stream f
  = unsafePerformIO
  $ evaluate (streamIn defaultContexts f)

-- | As 'stream', but execute in the specified context.
--
streamIn :: (Arrays a, Arrays b) => [Context] -> (Acc a -> Acc b) -> [a] -> [b]
streamIn ctxs f arrs = unsafePerformIO $ mapM waitSafe asyncs
  where
    !asyncs = streamAsyncIn ctxs f arrs

-- | As 'stream', but the computations are executed asynchronously.
--
streamAsync :: (Arrays a, Arrays b) => (Acc a -> Acc b) -> [a] -> [Async b]
streamAsync f
  = unsafePerformIO
  $ evaluate (streamAsyncIn defaultContexts f)


-- | As 'streamIn', but execute asynchronously.
--   Only compile and analyse the accelerate function once
streamAsyncIn :: (Arrays a, Arrays b) => [Context] -> (Acc a -> Acc b) -> [a] -> [Async b]
streamAsyncIn ctxs f arrs = unsafePerformIO $ mapM execute arrs
  where
    !acc  = convertAfunWith config f
    !ana  = analyseAfun acc (head arrs)
    --
    execute a = do
      !ctx       <- choseContextIn ctxs
      !afun      <- evalCUDA ctx (compileAfun acc) >>= dumpStats
      --
      push ana ctx
      evalCUDA ctx (executeAfun1 afun a >>= collectAsync)


-- Copy arrays from device to host asynchronously.
--
collectAsync :: forall arrs. Arrays arrs => Exec.Async arrs -> CIO (Async arrs)
collectAsync !arrs = do
  (Exec.Async event arr) <- Exec.streaming collect
  --
  ctx <- asks activeContext
  return $ Async event arr ctx
  where
    collect st = do
      arrs' <- Exec.after st arrs
      collectRAsync (arrays (undefined::arrs)) (fromArr arrs')
      return arrs'
      where
        collectRAsync :: ArraysR a -> a -> CIO ()
        collectRAsync ArraysRunit         ()             = return ()
        collectRAsync ArraysRarray        arr            = peekArrayAsync arr (Just st)
        collectRAsync (ArraysRpair r1 r2) (arrs1, arrs2) = collectRAsync r1 arrs1 >> collectRAsync r2 arrs2

-- How the Accelerate program should be interpreted.
-- TODO: make sharing/fusion runtime configurable via debug flags or otherwise.
--
config :: Phase
config =  Phase
  { recoverAccSharing      = True
  , recoverExpSharing      = True
  , floatOutAccFromExp     = True
  , enableAccFusion        = True
  , convertOffsetOfSegment = True
  }


dumpStats :: MonadIO m => a -> m a
#if ACCELERATE_DEBUG
dumpStats next = do
  stats <- liftIO simplCount
  liftIO $ traceMessage dump_simpl_stats (show stats)
  liftIO $ resetSimplCount
  return next
#else
dumpStats next = return next
#endif


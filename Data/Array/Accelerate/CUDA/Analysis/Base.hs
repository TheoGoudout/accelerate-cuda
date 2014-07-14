{-# LANGUAGE CPP                 #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE BangPatterns        #-}

module Data.Array.Accelerate.CUDA.Analysis.Base (

  -- * Environments
  Aenv(..), Env(..),
  aprj, prj,

  -- * Result arrays
  AnalysisAcc(..), AnalysisExp(..),
  expShape, accprj, expprj, reprSize,

  -- * Misc
  Analysis(..), Analysable(..),
  zero, one, analyseN, fold, reprToArr

) where

#include "accelerate.h"

import Data.Function                                    ( on )

import Data.Array.Accelerate.AST                        hiding ( prj, Empty, Push )
import Data.Array.Accelerate.Array.Sugar
import Data.Array.Accelerate.Tuple
import Data.Array.Accelerate.Type

--
--

data Analysis = Analysis {
      space         :: Int,
      time          :: Int,
      associativity :: Bool  -- TODO : split computation if possible
    } deriving (Eq)

instance Ord Analysis where
  compare a1 a2 =
    if time' /= EQ then time'
      else space'
    where
      space' = compare (space a1) (space a2)
      time'  = compare (time  a1) (time  a2)

{-# INLINE zero #-}
zero :: Analysis
zero = Analysis 0 0 True

{-# INLINE one #-}
one :: Analysis
one = Analysis 1 1 True

{-# INLINE analyseN #-}
analyseN :: Int -> Analysis
analyseN n = Analysis n n True

fold :: [Analysis] -> Analysis
fold []     = zero
fold (x:xs) = fold xs <+< x

-- | Environment of an array expression
-- Stocks all bounded variables
--
data Aenv aenv where
  Aempty :: Aenv ()
  Apush  :: Aenv aenv -> AnalysisAcc a -> Aenv (aenv, a)

aprj :: Idx aenv a -> Aenv aenv -> AnalysisAcc a
aprj idx' aenv = aprj' idx' aenv <<< one
  where
    aprj' :: Idx aenv a -> Aenv aenv -> AnalysisAcc a
    aprj' ZeroIdx        (_   `Apush` x) = x
    aprj' (SuccIdx !idx) (!xs `Apush` _) = aprj' idx xs
    aprj' _              _               = error "aprj : incorrect index"

-- | Environment of an expression
-- Stocks all bounded variables
--
data Env env where
  Empty :: Env ()
  Push  :: Env env -> AnalysisExp e -> Env (env, e)

prj :: Idx env a -> Env env -> AnalysisExp a
prj idx' aenv = prj' idx' aenv <<< one
  where
    prj' :: Idx env a -> Env env -> AnalysisExp a
    prj' ZeroIdx        (_   `Push` x) = x
    prj' (SuccIdx !idx) (!xs `Push` _) = prj' idx xs
    prj' _              _              = error "prj : incorrect index"


--
--
data AnalysisAcc a where
    AccRepr   :: Analysis
              -> ArrRepr a 
              -> AnalysisAcc a

    AccArray  :: (Shape sh, Elt e)
              => Analysis
              -> AnalysisExp sh 
              -> AnalysisExp e 
              -> AnalysisAcc (Array sh e)

    AccTuple  :: (IsTuple a) 
              => Analysis
              -> Atuple (AnalysisAcc) (TupleRepr a) 
              -> AnalysisAcc a


accprj :: TupleIdx (TupleRepr aenv) a -> AnalysisAcc aenv -> AnalysisAcc a
accprj idx (AccTuple _ atup) = accprj' idx atup <<< one -- Get reference to a variable is almost instantaneous
accprj _  _                  = INTERNAL_ERROR(error) "arrprj" "inconsistent valuation"

accprj' :: TupleIdx aenv a -> Atuple (AnalysisAcc) aenv -> AnalysisAcc a
accprj' ZeroTupIdx       (SnocAtup _ a) = a
accprj' (SuccTupIdx idx) (SnocAtup t _) = accprj' idx t
accprj' _                _              = error "arrprj : inconsistent valuation"

reprToArr :: (Shape sh, Elt e) => AnalysisAcc (Array sh e) -> AnalysisAcc (Array sh e)
reprToArr (AccRepr a repr) = AccArray a sh'' e''
  where
    arr@(Array sh _) = toArr repr
    --
    sh' = toElt sh
    e'  = arr ! sh'
    --
    sh'' = expShape zero sh'
    e''  = ExpRepr  zero (fromElt e')
reprToArr _ = INTERNAL_ERROR(error) "reprToArr" "inconsistent valuation"

--
--
data AnalysisExp e where
    ExpRepr   :: Elt e 
              => Analysis
              -> EltRepr e
              -> AnalysisExp e

    ExpTuple  :: IsTuple e 
              => Analysis
              -> Tuple (AnalysisExp) (TupleRepr e)
              -> AnalysisExp e

expShape :: (Elt sh, Shape sh) => Analysis -> sh -> AnalysisExp sh
expShape a sh = ExpRepr a (fromElt sh)

expprj :: (Elt t, IsTuple t, Elt e) => TupleIdx (TupleRepr t) e -> AnalysisExp t -> AnalysisExp e
expprj idx ex =
  case ex of
    ExpTuple _ tup -> tupprj  idx tup <<< one
    ExpRepr  _ _   -> reprprj idx ex  <<< one

tupprj :: TupleIdx t e -> Tuple (AnalysisExp) t -> AnalysisExp e
tupprj ZeroTupIdx       (SnocTup _ a) = a
tupprj (SuccTupIdx idx) (SnocTup t _) = tupprj idx t
tupprj _                _              = error "tupprj : inconsistent valuation"

reprprj :: forall t e. (Elt t, IsTuple t, Elt e) => TupleIdx (TupleRepr t) e -> AnalysisExp t -> AnalysisExp e
reprprj _   (ExpTuple _ _  ) = error "reprprj : inconsistent valuation" -- This is not supposed to happen...
reprprj idx (ExpRepr a repr) =
  if ix <= sz then ExpRepr a (fromElt (undefined::e)) 
    else error "reprprj : inconsistent valuation"
  where
    ix = tupleIdxToInt idx
    sz = reprSize (eltType (undefined::t)) repr

reprSize :: TupleType a -> a -> Int
reprSize UnitTuple         ()      = 0
reprSize (SingleTuple _)   _       = 1
reprSize (PairTuple t1 t2) (c1,c2) = reprSize t1 c1 + reprSize t2 c2




-- | Define data from which we can extract an analysis
-- Must implement analysis, one of (<+<) (>+>) and one of (<<<) (>>>)
--
class Analysable a where
  -- Get an Analysis out of this object
  analysis :: a -> Analysis

  -- Add analysis of both objects and put it back into the first object
  (<+<)    :: (Analysable b) => a -> b -> a
  (<+<)    = flip (>+>)

  -- Add analysis of both objects and put it back into the second object
  (>+>)    :: (Analysable b) => a -> b -> b
  (>+>)    = flip (<+<)

  -- Apply the second parameter to the analysis of the first one.
  -- (s,t,a) -> space * s, time * t, associativity && a
  (<*<)    :: a -> Analysis -> a
  (<*<)    =  flip (>*>)

  -- As (<*<) but with interverted parameters
  (>*>)    :: Analysis -> a -> a
  (>*>)    =  flip (<*<)

  -- Set the analysis of the first object
  (<<<)    :: a -> Analysis -> a
  (<<<)    =  flip (>>>)

  -- As (<<<) but with interverted parameters
  (>>>)    :: Analysis -> a -> a
  (>>>)    =  flip (<<<)

instance Analysable Analysis where
  analysis  = id
  (>>>)     = const

  a1 <+< a2 = let a2' = analysis a2 in
              Analysis  (space         a1 +  space         a2') 
                        (time          a1 +  time          a2')
                        (associativity a1 && associativity a2')

  a1 <*< a2 = let a2' = analysis a2 in
              Analysis  (space         a1 *  space         a2')
                        (time          a1 *  time          a2')
                        (associativity a1 && associativity a2')

instance Analysable (AnalysisAcc a) where
  analysis (AccRepr  a _  ) = a
  analysis (AccArray a _ _) = a
  analysis (AccTuple a _  ) = a

  a1@(AccRepr  _ repr) <+< a2 = AccRepr  (analysis a1 <+< analysis a2) repr
  a1@(AccArray _ sh e) <+< a2 = AccArray (analysis a1 <+< analysis a2) sh e
  a1@(AccTuple _ tup ) <+< a2 = AccTuple (analysis a1 <+< analysis a2) tup

  a1@(AccRepr  _ repr) <*< a2 = AccRepr  (analysis a1 <*< analysis a2) repr
  a1@(AccArray _ sh e) <*< a2 = AccArray (analysis a1 <*< analysis a2) sh e
  a1@(AccTuple _ tup ) <*< a2 = AccTuple (analysis a1 <*< analysis a2) tup

  (AccRepr  _ repr) <<< a = AccRepr  a repr
  (AccArray _ sh e) <<< a = AccArray a sh e
  (AccTuple _ tup ) <<< a = AccTuple a tup


instance Analysable (AnalysisExp e) where
  analysis (ExpRepr  a _) = a
  analysis (ExpTuple a _) = a

  e1@(ExpRepr  _ repr) <+< e2 = ExpRepr  (analysis e1 <+< analysis e2) repr
  e1@(ExpTuple _ tup ) <+< e2 = ExpTuple (analysis e1 <+< analysis e2) tup

  e1@(ExpRepr  _ repr) <*< e2 = ExpRepr  (analysis e1 <*< analysis e2) repr
  e1@(ExpTuple _ tup ) <*< e2 = ExpTuple (analysis e1 <*< analysis e2) tup

  (ExpRepr  _ repr) <<< a = ExpRepr  a repr
  (ExpTuple _ tup ) <<< a = ExpTuple a tup


-- | Needed for the Ord instance
--
instance Eq (AnalysisAcc a) where
  (==) = (==) `on` analysis

instance Eq (AnalysisExp a) where
  (==) = (==) `on` analysis

-- | In order to use the max operations
--
instance Ord (AnalysisAcc a) where
  compare = compare `on` analysis

instance Ord (AnalysisExp a) where
  compare = compare `on` analysis

-- | Display an analysis
--
instance Show Analysis where
  show (Analysis s t a) =
   "Analysis = { space = " ++ (show s ) ++
              ", time  = " ++ (show t ) ++
              ", assoc = " ++ (show a ) ++ "}"

instance Show (AnalysisAcc a) where
  show (AccRepr  a _  ) = "AccRepr  = {" ++ (show a) ++ "}"
  show (AccArray a _ _) = "AccArray = {" ++ (show a) ++ "}"
  show (AccTuple a _  ) = "AccTuple = {" ++ (show a) ++ "}"

instance Show (AnalysisExp e) where
  show (ExpRepr  a _) = "ExpRepr  = {" ++ (show a) ++ "}"
  show (ExpTuple a _) = "ExpTuple = {" ++ (show a) ++ "}"

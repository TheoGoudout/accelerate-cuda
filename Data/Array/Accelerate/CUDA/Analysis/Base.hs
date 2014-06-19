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
  expShape, accprj, expprj,

  -- * Misc
  Analysis(..), Analysable(..),
  zero, one, fold, (<*>), reprToArr

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

(<*>) :: Analysis -> (Int, Int) -> Analysis
(<*>) a (s,t) = Analysis (space a * s) (time a * t) (associativity a)

fold :: [Analysis] -> Analysis
fold []     = zero
fold (x:xs) = fold xs <+> x

--
--
data Aenv aenv where
  Aempty :: Aenv ()
  Apush  :: Aenv aenv -> AnalysisAcc a -> Aenv (aenv, a)

aprj :: Idx aenv a -> Aenv aenv -> AnalysisAcc a
aprj ZeroIdx        (_   `Apush` x) = x
aprj (SuccIdx !idx) (!xs `Apush` _) = aprj idx xs
aprj _              _               = INTERNAL_ERROR(error) "aprj" "inconsistent valuation"

--
--
data Env env where
  Empty :: Env ()
  Push  :: Env env -> AnalysisExp e -> Env (env, e)

prj :: Idx env a -> Env env -> AnalysisExp a
prj ZeroIdx        (_   `Push` x)  = x
prj (SuccIdx !idx) (!xs `Push` _) = prj idx xs
prj _              _              = INTERNAL_ERROR(error) "prj" "inconsistent valuation"


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
accprj idx (AccTuple a atup) = accprj' idx atup <<< a
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
expprj idx (ExpTuple a tup ) = tupprj idx tup <<< a
expprj idx  ex@(ExpRepr _ _) = reprprj idx ex

tupprj :: TupleIdx t e -> Tuple (AnalysisExp) t -> AnalysisExp e
tupprj ZeroTupIdx       (SnocTup _ a) = a
tupprj (SuccTupIdx idx) (SnocTup t _) = tupprj idx t
tupprj _                _              = error "tupprj : inconsistent valuation"

reprprj :: forall t e. (Elt t, IsTuple t, Elt e) => TupleIdx (TupleRepr t) e -> AnalysisExp t -> AnalysisExp e
reprprj _   (ExpTuple _ _  ) = error "reprprj : inconsistent valuation"
reprprj idx (ExpRepr a repr) =
  if ix <= sz then ExpRepr a (fromElt (undefined::e)) 
    else error "reprprj not implemented yet"
  where
    ix = tupleIdxToInt idx
    sz = reprSize (eltType (undefined::t)) repr

reprSize :: TupleType a -> a -> Int
reprSize UnitTuple         ()      = 0
reprSize (SingleTuple _)   _       = 1
reprSize (PairTuple t1 t2) (c1,c2) = reprSize t1 c1 + reprSize t2 c2

--
--
class Analysable a where
  analysis :: a -> Analysis

  (<+>)    :: (Analysable b) => a -> b -> a

  (<<<)    :: a -> Analysis -> a
  (<<<)    = flip (>>>)

  (>>>)    :: Analysis -> a -> a
  (>>>)    =  flip (<<<)

instance Analysable Analysis where
  analysis  = id
  (<<<)     = flip const

  a1 <+> a2 = let a2' = analysis a2 in
              Analysis  (space         a1 +  space         a2') 
                        (time          a1 +  time          a2')
                        (associativity a1 && associativity a2')


instance Analysable (AnalysisAcc a) where
  analysis (AccRepr  a _  ) = a
  analysis (AccArray a _ _) = a
  analysis (AccTuple a _  ) = a

  a1@(AccRepr  _ repr) <+> a2 = AccRepr  (analysis a1 <+> analysis a2) repr
  a1@(AccArray _ sh e) <+> a2 = AccArray (analysis a1 <+> analysis a2) sh e
  a1@(AccTuple _ tup ) <+> a2 = AccTuple (analysis a1 <+> analysis a2) tup

  (AccRepr  _ repr) <<< a = AccRepr  a repr
  (AccArray _ sh e) <<< a = AccArray a sh e
  (AccTuple _ tup ) <<< a = AccTuple a tup


instance Analysable (AnalysisExp e) where
  analysis (ExpRepr  a _) = a
  analysis (ExpTuple a _) = a

  e1@(ExpRepr  _ repr) <+> e2 = ExpRepr  (analysis e1 <+> analysis e2) repr
  e1@(ExpTuple _ tup ) <+> e2 = ExpTuple (analysis e1 <+> analysis e2) tup

  (ExpRepr  _ repr) <<< a = ExpRepr  a repr
  (ExpTuple _ tup ) <<< a = ExpTuple a tup


--
--
instance Eq (AnalysisAcc a) where
  (==) = (==) `on` analysis

instance Eq (AnalysisExp a) where
  (==) = (==) `on` analysis

--
--
instance Ord (AnalysisAcc a) where
  compare = compare `on` analysis

instance Ord (AnalysisExp a) where
  compare = compare `on` analysis

--
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

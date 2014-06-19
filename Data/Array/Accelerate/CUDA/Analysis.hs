{-# LANGUAGE CPP                   #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE BangPatterns          #-}
{-# LANGUAGE TypeOperators         #-}

module Data.Array.Accelerate.CUDA.Analysis (

  -- * Analysis structures
  AnalysisAcc(..), Analysable(..),

  -- * Analysis functions
  analyseAcc, analyseAfun, analyseArr,

  -- * Misc
  fold, zero

) where

#include "accelerate.h"

import Data.Array.Accelerate.AST            hiding ( prj, Empty, Push )
import Data.Array.Accelerate.Trafo
import Data.Array.Accelerate.Tuple
import Data.Array.Accelerate.Type
import Data.Array.Accelerate.Array.Sugar

import Data.Array.Accelerate.CUDA.Analysis.Base

-- | 
--
analyseAcc :: DelayedAcc a -> AnalysisAcc a
analyseAcc acc = analyseOpenAcc acc Aempty

-- |
--
analyseAfun :: (Arrays a, Arrays b) => DelayedAfun (a -> b) -> a -> AnalysisAcc b
analyseAfun !afun !arrs = analyseOpenAfun afun Aempty arg
  where
    !arg = analyseArr (arrays arrs) (fromArr arrs)

-- |
--
analyseArr :: forall a. ArraysR (ArrRepr a) -> ArrRepr a -> AnalysisAcc a
analyseArr !arrs !repr = AccRepr (analyseArr' arrs repr) repr
  where
    analyseArr' :: ArraysR a' -> a' -> Analysis
    analyseArr' ArraysRunit         ()       = zero
    analyseArr' (ArraysRpair a1 a2) (r1, r2) = analyseArr' a1 r1 <+> analyseArr' a2 r2
    analyseArr' ArraysRarray        arr      = Analysis s s True 
      where
        toShape :: (Shape sh, Elt e) => (Array sh e) -> sh
        toShape (Array sh _) = toElt sh 
        --
        s = size $ toShape arr

--
analyseOpenAfun :: DelayedOpenAfun aenv (a -> b) -> Aenv aenv -> AnalysisAcc a -> AnalysisAcc b
analyseOpenAfun (Alam (Abody b)) !aenv !x = analyseOpenAcc b (aenv `Apush` x)
analyseOpenAfun _                _     _  = INTERNAL_ERROR(error) "analyseOpenAfun" "pattern mismatched"

analyseOpenAcc :: DelayedOpenAcc aenv a -> Aenv aenv -> AnalysisAcc a
analyseOpenAcc = traverseAcc
  where
    traverseAcc :: forall aenv arrs. DelayedOpenAcc aenv arrs -> Aenv aenv -> AnalysisAcc arrs
    traverseAcc Delayed{}               _     = INTERNAL_ERROR(error) "analyseOpenAcc" "unexpected delayed array"
    traverseAcc !topAcc@(Manifest pacc) !aenv =
      case pacc of
        -- Environment and control flow
        Avar ix                 -> aprj ix aenv
        Alet a b                -> let bnd = travA a in traverseAcc b (aenv `Apush` bnd) <+> bnd
        Apply f a               -> analyseOpenAfun f aenv (travA a)
        Awhile p f a            -> mkAwhile p f (travA a)
        Acond p t e             -> max (travA t) (travA e) <+> (travE p)
        Atuple tup              -> travAtup tup
        Aprj ix tup             -> accprj ix (travA tup)

        -- Foreign
        Aforeign ff afun a      -> error "Aforeign"

        -- Array injection
        Unit e                  -> unit e
        Use arrs                -> analyseArr (arrays (undefined::arrs)) arrs
        
        -- Index space transforms
        Reshape s a             -> error "Reshape"
        Replicate slix e a      -> error "Replicate"
        Slice slix a e          -> error "Slice"
        Backpermute e f a       -> error "Backpermute"

        -- Producers
        Generate e f            -> mkGenerate  f (travE e)
        Map f a                 -> mkMap       f (travA a)
        ZipWith f a b           -> mkZipWith   f (travA a) (travA b)
        Transform e p f a       -> mkTransform p (travE e)           f (travA a)

        -- Consumers
        Fold f z a              -> mkFold  f (travE z) (travA a)
        Fold1 f a               -> mkFold1 f           (travA a)
        FoldSeg f e a s         -> error "FoldSeg"
        Fold1Seg f a s          -> error "Fold1Seg"
        Scanl f e a             -> mkScan  f (travE e) (travA a)
        Scanl' f e a            -> error "Scanl'"
        Scanl1 f a              -> mkScan1 f           (travA a)
        Scanr f e a             -> mkScan  f (travE e) (travA a)
        Scanr' f e a            -> error "Scanr'"
        Scanr1 f a              -> mkScan1 f           (travA a)
        Permute f d g a         -> error "Permute"
        Stencil f b a           -> error "Stencil"
        Stencil2 f b1 a1 b2 a2  -> error "Stencil"

      where
        unit :: Elt e => DelayedOpenExp () aenv e -> AnalysisAcc (Scalar e)
        unit e = AccArray (Analysis 1 0 True) (expShape zero Z) (travE e)

        travE :: DelayedOpenExp () aenv e -> AnalysisExp e
        travE ex = analyseOpenExp ex Empty aenv

        travAtup :: IsTuple a => Atuple (DelayedOpenAcc aenv) (TupleRepr a) -> AnalysisAcc a
        travAtup tup = let (tupl, a) = travAtup' tup in AccTuple a tupl
          where
            travAtup' :: Atuple (DelayedOpenAcc aenv) a -> (Atuple (AnalysisAcc) a, Analysis)
            travAtup' NilAtup        = (NilAtup, zero)
            travAtup' (SnocAtup t a) = (SnocAtup tup' arr, a1 <+> analysis arr)
              where
                (tup', a1) = travAtup' t
                arr       = travA a

        travA :: DelayedOpenAcc aenv a -> AnalysisAcc a
        travA acc = case acc of
          Manifest{}    -> traverseAcc acc aenv
          Delayed{..}   -> mkDelayed indexD (travE extentD)

        --

        mkDelayed
          :: (Shape sh, Elt e)
          => DelayedOpenFun () aenv (sh -> e)
          -> AnalysisExp sh
          -> AnalysisAcc (Array sh e)
        mkDelayed 
          (Lam (Body b)) sh
            = AccArray a sh ex
          where
            env = Empty `Push` sh
            ex  = analyseOpenExp b env aenv
            a   = analysis sh <+> analysis ex       -- FIXME
        mkDelayed _ _ = INTERNAL_ERROR(error) "mkDelayed" "inconsistent valuation"

        --

        mkAwhile
          :: Arrays arrs
          => DelayedOpenAfun aenv (arrs -> Scalar Bool)
          -> DelayedOpenAfun aenv (arrs -> arrs)
          -> AnalysisAcc arrs
          -> AnalysisAcc arrs
        mkAwhile
          (Alam (Abody b1))
          (Alam (Abody b2))
          arr
            = arr <+> a
          where
            aenv' = aenv `Apush` arr
            ex1   = analyseOpenAcc b1 aenv'
            ex2   = analyseOpenAcc b2 aenv'
            a     = analysis ex1 <+> analysis ex2
        mkAwhile _ _ _ = INTERNAL_ERROR(error) "mkAwhile" "inconsistent valuation"

        mkGenerate 
          :: (Shape sh, Elt e)
          => DelayedOpenFun () aenv (sh -> e)
          -> AnalysisExp sh
          -> AnalysisAcc (Array sh e)
        mkGenerate
          (Lam (Body !b)) !sh
            = AccArray a sh ex
          where
            env = Empty `Push` sh
            !ex = analyseOpenExp b env aenv
            a   = analysis sh <+> analysis ex      -- FIXME
        mkGenerate _ _ = INTERNAL_ERROR(error) "mkGenerate" "inconsistent valuation"

        mkMap   
          :: (Shape sh, Elt e, Elt e')
          => DelayedOpenFun () aenv (e -> e') 
          -> AnalysisAcc (Array sh e) 
          -> AnalysisAcc (Array sh e')
        mkMap 
          (Lam (Body !b)) 
          !arr@(AccArray _ !sh !arg) 
            = AccArray a sh ex
          where
            !env = Empty `Push` arg
            !ex  = analyseOpenExp b env aenv
            !a   = analysis arr <+> analysis ex      -- FIXME
        mkMap _ _ = INTERNAL_ERROR(error) "mkMap" "inconsistent valuation"

        mkZipWith 
          :: (Shape sh, Elt e1, Elt e2, Elt e3) 
          => DelayedOpenFun () aenv (e1 -> e2 -> e3) 
          -> AnalysisAcc (Array sh e1) 
          -> AnalysisAcc (Array sh e2) 
          -> AnalysisAcc (Array sh e3)
        mkZipWith 
          (Lam (Lam (Body b))) 
          arr1@(AccArray a1 (ExpRepr a3 repr1) arg1)
          arr2@(AccArray a2 (ExpRepr a4 repr2) arg2)
            = AccArray a sh ex
          where
            env = Empty `Push` arg1 `Push` arg2
            ex  = analyseOpenExp b env aenv
            sh  = expShape (a3 <+> a4) (intersect (toElt repr1) (toElt repr2))
            a   = analysis ex <+> analysis arr1 <+> analysis arr2
        mkZipWith _ _ _ = INTERNAL_ERROR(error) "mkZipWith" "inconsistent valuation"

        mkTransform 
          :: (Shape sh, Shape sh', Elt a, Elt b) 
          => DelayedOpenFun () aenv (sh' -> sh)
          -> AnalysisExp sh'
          -> DelayedOpenFun () aenv (a   -> b)
          -> AnalysisAcc (Array sh a)
          -> AnalysisAcc (Array sh' b)
        mkTransform
          (Lam (Body b1)) sh1
          (Lam (Body b2)) arr@(AccArray a1 sh2 elt)
            = AccArray a sh1 ex2
          where
            env1 = Empty `Push` sh1
            ex1  = analyseOpenExp b1 env1 aenv -- FIXME
            --
            env2 = Empty `Push` elt
            ex2  = analyseOpenExp b2 env2 aenv
            --
            a    = analysis ex1 <+> analysis ex2 <+> analysis sh1 <+> analysis arr
        mkTransform _ _ _ _ = INTERNAL_ERROR(error) "mkTransform" "inconsistent valuation"

        --

        mkFold
          :: (Shape sh, Elt e)
          => DelayedOpenFun () aenv (e -> e -> e)
          -> AnalysisExp e
          -> AnalysisAcc (Array (sh:.Int) e)
          -> AnalysisAcc (Array sh e)
        mkFold 
          (Lam (Lam (Body b))) 
          !arr1 
          !arr2@(AccArray _ (ExpRepr a1 (repr,_)) !elt) 
            = AccArray a repr' ex
          where
            env   = Empty `Push` arr1 `Push` elt
            !ex    = analyseOpenExp b env aenv
            repr' = ExpRepr a1 repr
            a     = analysis ex <+> analysis arr1 <+> analysis arr2
        mkFold _ _ _ = INTERNAL_ERROR(error) "mkFold" "inconsistent valuation"

        mkFold1
          :: (Shape sh, Elt e)
          => DelayedOpenFun () aenv (e -> e -> e)
          -> AnalysisAcc (Array (sh:.Int) e)
          -> AnalysisAcc (Array sh e)
        mkFold1 !f !acc@(AccArray _ _ ex) = mkFold f ex acc
        mkFold1 _ _ = INTERNAL_ERROR(error) "mkFold1" "inconsistent valuation"

        mkScan
          :: Elt e
          => DelayedOpenFun () aenv (e -> e -> e)
          -> AnalysisExp e
          -> AnalysisAcc (Vector e)
          -> AnalysisAcc (Vector e)
        mkScan 
          (Lam (Lam (Body b))) 
          arg 
          arr@(AccArray _ sh elt) 
            = AccArray a sh ex
          where
            env = Empty `Push` arg `Push` elt
            ex  = analyseOpenExp b env aenv
            a   = analysis ex <+> analysis arg <+> analysis arr
        mkScan _ _ _ = INTERNAL_ERROR(error) "mkScan" "inconsistent valuation"

        mkScan1
          :: Elt e
          => DelayedOpenFun () aenv (e -> e -> e)
          -> AnalysisAcc (Vector e)
          -> AnalysisAcc (Vector e)
        mkScan1 f acc@(AccArray _ _ ex) = mkScan f ex acc
        mkScan1 _ _ = INTERNAL_ERROR(error) "mkScan1" "inconsistent valuation"


analyseOpenExp :: DelayedOpenExp env aenv e -> Env env -> Aenv aenv -> AnalysisExp e
analyseOpenExp = traverseExp
  where
    traverseExp :: forall env aenv exp. DelayedOpenExp env aenv exp -> Env env -> Aenv aenv -> AnalysisExp exp
    traverseExp !ex !env !aenv =
      case ex of
        Var ix                  -> prj ix env
        Const c                 -> travConst (eltType (undefined::exp)) c
        PrimConst c             -> error "PrimConst"
        IndexAny                -> error "IndexAny"
        IndexNil                -> expShape zero Z
        Foreign ff f x          -> error "Foreign"
        --
        Let a b                 -> let bnd = travE a in traverseExp b (env `Push` bnd) aenv <+> bnd
        IndexCons t h           -> error "IndexCons"
        IndexHead h             -> mkIndexHead (travE h)
        IndexTail t             -> mkIndexTail (travE t)
        IndexSlice slix x s     -> error "IndexSlice"
        IndexFull slix x s      -> error "IndexFull"
        ToIndex s i             -> error "ToIndex"
        FromIndex s i           -> error "FromIndex"
        Tuple t                 -> travT t
        Prj ix e                -> expprj ix (travE e)
        Cond p t e              -> max (travE t) (travE e) <+> (travE p)
        While p f x             -> mkWhile p f (travE x)
        PrimApp f e             -> travP f (travE e)
        Index a e               -> mkIndex (travA a) (travE e)
        LinearIndex a e         -> error "LinearIndex"
        Shape a                 -> mkShape (travA a)
        ShapeSize e             -> error "ShapeSize"
        Intersect x y           -> error "Intersect"

      where
        travA :: DelayedOpenAcc aenv a -> AnalysisAcc a
        travA = flip analyseOpenAcc aenv

        travT :: IsTuple t => Tuple (DelayedOpenExp env aenv) (TupleRepr t) -> AnalysisExp t
        travT !tup = let (tupl,a) = travT' tup in ExpTuple a tupl
          where
            travT' :: Tuple (DelayedOpenExp env aenv) t -> (Tuple (AnalysisExp) t, Analysis)
            travT' !NilTup         = (NilTup,zero)
            travT' (SnocTup !t !e) = (SnocTup tup' ex', a <+> analysis ex')
              where
                (!tup', !a) = travT' t
                !ex'        = travE e

        travP :: (Elt a, Elt r) => PrimFun (a -> r) -> AnalysisExp a -> AnalysisExp r
        travP = analysePrim

        travE :: DelayedOpenExp env aenv e -> AnalysisExp e
        travE = \acc -> traverseExp acc env aenv

        travConst :: Elt e => TupleType (EltRepr e) -> EltRepr e -> AnalysisExp e
        travConst !ty !c = ExpRepr (travConst' ty c) c
          where
            travConst' :: TupleType a -> a -> Analysis
            travConst' UnitTuple           !_       = zero
            travConst' (SingleTuple _)     !_       = Analysis 1 0 True
            travConst' (PairTuple ty1 ty0) !(cs,c') = travConst' ty1 cs <+> travConst' ty0 c'

        --

        mkWhile
          :: Elt e
          => DelayedOpenFun env aenv (e -> Bool)
          -> DelayedOpenFun env aenv (e -> e)
          -> AnalysisExp e
          -> AnalysisExp e
        mkWhile
          (Lam (Body b1))
          (Lam (Body b2))
          elt
            = elt <+> a
          where
            env' = env `Push` elt
            ex1  = analyseOpenExp b1 env' aenv
            ex2  = analyseOpenExp b2 env' aenv
            a    = analysis ex1 <+> analysis ex2
        mkWhile _ _ _ = INTERNAL_ERROR(error) "mkWhile" "inconsistent valuation"

        mkShape
          :: (Shape sh, Elt e)
          => AnalysisAcc (Array sh e)
          -> AnalysisExp sh
        mkShape (AccArray a !sh _)  = sh <<< a
        mkShape !repr@(AccRepr _ _) = mkShape (reprToArr repr)
        mkShape _                  = INTERNAL_ERROR(error) "mkShape" "shape of Atuple requested"

        mkIndex
          :: (Shape dim, Elt t)
          => AnalysisAcc (Array dim t)
          -> AnalysisExp dim
          -> AnalysisExp t
        mkIndex (AccArray a _ !expr)  _ = expr <<< a -- FIXME
        mkIndex !repr@(AccRepr _ _ ) !d = mkIndex (reprToArr repr) d
        mkIndex _                   _ = INTERNAL_ERROR(error) "mkIndex" "inconsistent valuation"

        mkIndexHead
          :: forall e sl.
             (Slice sl, Elt e)
          => AnalysisExp (sl:.e)
          -> AnalysisExp e
        mkIndexHead (ExpRepr a (_,_)) = ExpRepr a (fromElt (undefined::e))
        mkIndexHead _                 = INTERNAL_ERROR(error) "mkIndexHead" "inconsistent valuation"

        mkIndexTail
          :: (Slice sl, Elt a)
          => AnalysisExp (sl:.a)
          -> AnalysisExp sl
        mkIndexTail (ExpRepr a (sl,_)) = ExpRepr a sl
        mkIndexTail _                   = INTERNAL_ERROR(error) "mkIndexTail" "inconsistent valuation"


analysePrim :: forall a r. (Elt a, Elt r) => PrimFun (a -> r) -> AnalysisExp a -> AnalysisExp r
analysePrim !p !ex = -- FIXME : pattern matching over repr
  case ex of
    ExpTuple a (NilTup `SnocTup` _)             -> analysePrim1 p a 
    ExpTuple a (NilTup `SnocTup` _ `SnocTup` _) -> analysePrim2 p a
    ExpTuple _ _                                -> error "analysePrim : pattern mismatched"
    --
    ExpRepr  a repr                             ->
      if lengthEltRepr (eltType (undefined::a)) repr == 1 then analysePrim1 p a
        else if lengthEltRepr (eltType (undefined::a)) repr == 2 then analysePrim2 p a
          else error "analysePrim : pattern mismatched"
  where
    -- Function that needs two arguments
    analysePrim2 :: PrimFun (a -> r) -> Analysis -> AnalysisExp r
    analysePrim2 !prim !a =
      case prim of
        PrimAdd              _ -> createExpRepr a
        PrimSub              _ -> createExpRepr a
        PrimMul              _ -> createExpRepr a
        PrimQuot             _ -> createExpRepr a
        PrimRem              _ -> createExpRepr a
        PrimIDiv             _ -> createExpRepr a
        PrimMod              _ -> createExpRepr a
        PrimBAnd             _ -> createExpRepr a
        PrimBOr              _ -> createExpRepr a
        PrimBXor             _ -> createExpRepr a
        PrimBShiftL          _ -> createExpRepr a
        PrimBShiftR          _ -> createExpRepr a
        PrimBRotateL         _ -> createExpRepr a
        PrimBRotateR         _ -> createExpRepr a
        PrimFDiv             _ -> createExpRepr a
        PrimFPow             _ -> createExpRepr a
        PrimLogBase          _ -> createExpRepr a
        PrimAtan2            _ -> createExpRepr a
        PrimMax              _ -> createExpRepr a
        PrimMin              _ -> createExpRepr a
        PrimLt               _ -> createExpRepr a
        PrimGt               _ -> createExpRepr a
        PrimLtEq             _ -> createExpRepr a
        PrimGtEq             _ -> createExpRepr a
        PrimEq               _ -> createExpRepr a
        PrimNEq              _ -> createExpRepr a
        PrimLAnd               -> createExpRepr a
        PrimLOr                -> createExpRepr a
        _                      -> error "analysePrim : pattern mismatched"


    -- Function that needs one argument
    analysePrim1 :: PrimFun (a -> r) -> Analysis -> AnalysisExp r
    analysePrim1 !prim !a =
      case prim of
        PrimNeg              _ -> createExpRepr a
        PrimAbs              _ -> createExpRepr a
        PrimSig              _ -> createExpRepr a
        PrimBNot             _ -> createExpRepr a
        PrimRecip            _ -> createExpRepr a
        PrimSin              _ -> createExpRepr a
        PrimCos              _ -> createExpRepr a
        PrimTan              _ -> createExpRepr a
        PrimAsin             _ -> createExpRepr a
        PrimAcos             _ -> createExpRepr a
        PrimAtan             _ -> createExpRepr a
        PrimAsinh            _ -> createExpRepr a
        PrimAcosh            _ -> createExpRepr a
        PrimAtanh            _ -> createExpRepr a
        PrimExpFloating      _ -> createExpRepr a
        PrimSqrt             _ -> createExpRepr a
        PrimLog              _ -> createExpRepr a
        PrimTruncate       _ _ -> createExpRepr a
        PrimRound          _ _ -> createExpRepr a
        PrimFloor          _ _ -> createExpRepr a
        PrimCeiling        _ _ -> createExpRepr a
        PrimFromIntegral   _ _ -> createExpRepr a
        PrimLNot               -> createExpRepr a
        PrimOrd                -> createExpRepr a
        PrimChr                -> createExpRepr a
        PrimBoolToInt          -> createExpRepr a
        _                      -> error "analysePrim : pattern mismatched"

    -- Creates resulting  AnalysisExp
    createExpRepr :: Elt r => Analysis -> AnalysisExp r
    createExpRepr a' = ExpRepr a' (fromElt (undefined::r))

    -- Compute the length of a TupleType
    lengthEltRepr :: TupleType a' -> a' -> Int
    lengthEltRepr UnitTuple           _       = 0
    lengthEltRepr (SingleTuple _)     _       = 1
    lengthEltRepr (PairTuple ty1 ty0) (c0,c1) = lengthEltRepr ty1 c0 + lengthEltRepr ty0 c1

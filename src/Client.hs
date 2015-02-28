{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
module Client where

import Data.Foldable (Foldable)
import qualified Data.Foldable as Foldable
import Data.Traversable (Traversable)
import qualified Data.Traversable as Traversable

import Data.Typeable
import Control.Monad
import Control.Monad.Catch

import UnifierSig
import qualified SolverHi as Hi

-- Synatx of System F
import qualified F

-- Syntax of the untyped calculus (ML)
import qualified ML

type TermVar = Hi.TermVar

               

type Var s = Hi.Var s

data Structure a =
    TyArrow a a
  | TyProduct a a
    deriving (Functor, Foldable, Traversable, Typeable, Show)

instance ZipM Structure where
  zipM_ f (TyArrow t1 t2) (TyArrow u1 u2) = do
    f t1 t2
    f t1 u2
  zipM_ f (TyProduct t1 t2) (TyProduct u1 u2) = do
    f t1 t2
    f u1 u2
  zipM_ f t1 t2 = throwM $ ZipError t1 t2


  zipM f (TyArrow t1 t2) (TyArrow u1 u2) = do
    liftM2 TyArrow (f t1 t2) (f t1 t2)
  zipM f (TyProduct t1 t2) (TyProduct u1 u2) = do
    liftM2 TyProduct (f t1 t2) (f u1 u2)
  zipM f t1 t2 = throwM $ ZipError t1 t2

instance Output F.NominalType where
  type Src F.NominalType = Structure

  tovar = F.TyVar
  
  struc (TyArrow t1 t2)   = (F.TyArrow t1 t2)
  struc (TyProduct t1 t2) = (F.TyProduct t1 t2)

type TyVar = Int

--------------------------------------------------------------------------

-- smart constructor for let
flet x (F.Var y) u | x == y = u
flet x t u = F.Let x t u

-- eta-reducing smart constructor for type abstraction
ftyabs1 v (F.TyApp t (F.TyVar w)) | v == w = t
ftyabs1 v t = F.TyAbs v t

--------------------------------------------------------------------------

type Coercion = F.NominalTerm -> F.NominalTerm

bottom :: F.NominalType
bottom = F.TyForall 0 (F.TyVar 0)    -- forall a.a

coerce :: [TyVar] -> [TyVar] -> Coercion
coerce vs1 vs2 t = undefined
{-
  foldr ftyabs1 vs2 (F.ftyapp t (map suitable vs1)) where
    suitable v =
     if  v `elem` vs2 then F.TyVar v else bottom
-}
--------------------------------------------------------------------------

type Variable = Hi.Var Structure

type Co a = Hi.Co F.NominalType a

hastype :: ML.Tm -> Variable -> IO (Co F.NominalTerm)
hastype (ML.Var x) tau = do
  c <- (Hi.inst x tau)
  return $ fmap (F.ftyapp (F.Var x)) c
hastype (ML.Abs x u) tau =
  (tau1, (tau2 ((), u'))) <- 
    exist (\ v1 ->
            exist ( \ v2 ->
                     tau -==- TyArrow v1 v2 ^&
                     def x v1 (hastype u v2)))
  return $ fmap (F.Abs x tau1 u')

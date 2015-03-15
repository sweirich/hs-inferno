{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Client where

import Prelude hiding ((^^))

import Control.Monad

import Language.Inferno.Solver 
 
import Data.List(intersperse)

-- Synatx of System F
import qualified F

-- Syntax of the untyped calculus (ML)
import qualified ML

-- Top-level structure of types that the unifier works with
data Structure a =
    TyArrow a a
  | TyProduct a a
  | TyBool
    deriving (Functor, Foldable, Traversable, Typeable, Show, Eq)

instance ZipM Structure where
  zipM_ f TyBool TyBool = return ()
  zipM_ f (TyArrow t1 t2) (TyArrow u1 u2) = do
    f t1 u1
    f t2 u2
  zipM_ f (TyProduct t1 t2) (TyProduct u1 u2) = do
    f t1 u1
    f t2 u2
  zipM_ f t1 t2 = throwM $ ZipError t1 t2

  zipM f TyBool TyBool = return TyBool
  zipM f (TyArrow t1 t2) (TyArrow u1 u2) = do
    liftM2 TyArrow (f t1 u1) (f t2 u2)
  zipM f (TyProduct t1 t2) (TyProduct u1 u2) = do
    liftM2 TyProduct (f t1 u1) (f t2 u2)
  zipM f t1 t2 = throwM $ ZipError t1 t2

instance Output F.NominalType where
  type Src F.NominalType = Structure

  tovar = F.TyVar

  struc (TyBool)          = F.TyBool
  struc (TyArrow t1 t2)   = (F.TyArrow t1 t2)
  struc (TyProduct t1 t2) = (F.TyProduct t1 t2)

type TyVar = Int

--------------------------------------------------------------------------

-- smart constructor for let
flet x a b (F.Var y) u | x == y = u
flet x a b t u = F.Let x a b t u

-- eta-reducing smart constructor for type abstraction
ftyabs1 :: TyVar -> F.NominalTerm -> F.NominalTerm
ftyabs1 v (F.TyApp t (F.TyVar w)) | v == w = t
ftyabs1 v t = F.TyAbs v t

--------------------------------------------------------------------------

type Coercion = F.NominalTerm -> F.NominalTerm

bottom :: F.NominalType
bottom = F.TyForall 0 (F.TyVar 0)    -- forall a.a

coerce :: [TyVar] -> [TyVar] -> Coercion
coerce vs1 vs2 t = 
  foldr ftyabs1 app vs2 where
    app :: F.NominalTerm
    app = F.ftyapp t (map suitable vs1)
    suitable v =
     if  v `elem` vs2 then F.TyVar v else bottom

--------------------------------------------------------------------------

type Variable = Var Structure

type C = Co F.NominalType F.NominalTerm

product_i 1 t u = TyProduct t u
product_i 2 t u = TyProduct u t


hastype :: ML.Tm -> Variable -> M C
hastype (ML.Var x) tau = do
  (inst x tau)
    <$$> (\vs -> F.ftyapp (F.Var x) vs) 
hastype (ML.Abs x u) tau = do
  (exist (\ v1 ->
      exist (\ v2 -> do
          c1 <- tau -==- TyArrow v1 v2
          c2 <- hastype u v2
          return (c1 ^^ def x (trivial v1) c2))))
    <$$>  \ (tau1, (tau2, u)) -> F.Abs x tau1 u
hastype (ML.App t1 t2) tau = do
  exist (\v -> do
               c1 <- liftS hastype t1 (TyArrow v tau)
               c2 <- hastype t2 v
               return $ c1 ^& c2)
    <$$> (\ (_, (t1', t2')) -> F.App t1' t2') 

hastype (ML.Let x t u) tau = do
  -- construct a (non-recursive) let constraint
  cu <- hastype u tau
  c <- (let1 False x (hastype t) cu)
  return $ fmap (\ (a, t', (b, s), u') ->
           F.Let x b s (F.ftyabs a t')
              (flet x b s (coerce a b (F.Var x)) u')) c
    
  
hastype (ML.Pair t1 t2) tau = do
  c <- exist_ (\ v1 ->
         exist_ (\ v2 -> do
            -- [tau] must be the product type [v1 * v2]
            c1 <- tau -==- TyProduct v1 v2
            c2 <- hastype t1 v2
            c3 <- hastype t2 v2
            return $ c1 ^^ c2 ^& c3))
  return $ fmap (\ (t1, t2) -> F.Pair t1 t2) c
  
hastype (ML.Proj i t) tau =  do
  c <- exist_ (\ other -> 
         liftS hastype t (product_i i tau other))
  return $ fmap (\t -> F.Proj i t) c

hastype (ML.Bool b) tau = do
  c <- tau -==- TyBool
  return $ fmap (\ () -> F.Bool b) c

hastype (ML.If e1 e2 e3) tau = do
  c1 <- liftS hastype e1 TyBool
  c2 <- hastype e2 tau
  c3 <- hastype e3 tau
  return $ fmap (\ ((t1,t2),t3) ->
                  F.If t1 t2 t3) (c1 ^& c2 ^& c3)

-------------------------------------------------------------
constraints t = do
  c  <- exist_ (hastype t)
  c2 <- let0 c
  return $ fmap (\(vs,t) -> F.ftyabs vs t) c2
  
translate t = do
  c3 <- constraints t
  solve False c3

inf = runSolverM . translate

----------------------------------------------------------
-- some test cases  

ml1 :: ML.Tm
ml1 = ML.Abs "x" (ML.Var "x")

ml2 = ML.Abs "f" (ML.Abs "x"
      (ML.App (ML.Var "f") (ML.Var "x")))

ml3 = ML.Let "id" ml1
       (ML.Pair (ML.App (ML.Var "id") (ML.Bool True))
        (ML.App (ML.Var "id") (ML.Pair (ML.Bool True) (ML.Bool False))))


x =
  ML.Var "x"

y =
  ML.Var "y"

mlid =
  ML.Abs "x" x

delta =
  ML.Abs "x" (ML.App x x)

deltadelta =
  ML.App delta delta

idid =
  ML.App mlid mlid

k =
  ML.Abs "x" (ML.Abs "y" x)

genid =
  ML.Let "x" mlid x

genidid =
  ML.Let "x" mlid (ML.App x x)

genkidid =
  ML.Let "x" (ML.App k mlid) (ML.App x mlid)

genkidid2 =
  ML.Let "x" (ML.App (ML.App k mlid) mlid) x

app_pair = -- ill-typed 
  ML.App (ML.Pair mlid mlid) mlid

mlnot = ML.Abs "x" (ML.If x (ML.Bool False) (ML.Bool True))



test = do
  mapM_ inf
    [mlid,
     delta,
     deltadelta,
     idid,
     k,
     genid, genidid, genkidid, genkidid2, mlnot]

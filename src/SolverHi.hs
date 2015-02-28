{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -fdefer-type-errors #-}
module SolverHi where

-- import Data.IORef
import Control.Monad
import Control.Applicative

import Control.Monad.Ref

-- The Structure and Output classes
import Data.Traversable (Traversable)
import UnifierSig

-- We rely on the low-level solver interface
import qualified SolverLo as Lo

type TermVar = Lo.TermVar
type Var s = Lo.Var s

{- We now set up the applicative functor API, or combinator API, to the
   solver. The constraint construction phase and the witness decoding phase
   are packaged together, with two benefits: 1- the syntax of constraints and
   witnesses, as well as the details of write-once references, are hidden; 2-
   the client can write code in a compositional and declarative style, under
   the illusion that constructing a query immediately gives rise to an
   answer. 

   The client is allowed to construct objects of type ['a co]. Such an object is
   a pair of a constraint and a continuation. It is evaluated in two phases. In
   the first phase, the constraint is solved. In the second phase, the continuation
   is invoked. It is allowed to examine the witness, and must produce a value of
   type ['a]. 

   The continuation has access to an environment of type [env]. For the moment,
   the environment is just a type decoder.  -}

type Env t = Lo.Decoder t

data Co t a = Co (Lo.RawCo (Src t)) (Env t -> IO a)

--------------------------------------------------------------------------

-- the type forms an applicative functor

instance (Functor (Co t)) where
  fmap f (Co rc k) = Co rc  (\env -> liftM f (k env))

-- the pairing operation (from McBride & Patterson's Monoidal class)
  
(Co rc1  k1) ^& (Co rc2 k2) =
  Co (Lo.CConj rc1 rc2) (\env -> liftM2 (,) (k1 env) (k2 env))

-- a variant of the above which builds a conjunction constraint
-- but drops the frist component of the pair and keeps only the second.

(Co rc1  k1) ^^ (Co rc2 k2) =
  Co (Lo.CConj rc1 rc2) (\env -> (k1 env) >> (k2 env))

instance (Applicative (Co t)) where
  pure x = (Co Lo.CTrue (\ env -> return x))
  mf <*> mx = fmap (\(f,x) -> f x) (mf ^& mx)

-- the Co type does not form a monoid. There is no bind.

--------------------------------------------------------------------------

-- existential quantification

-- exist_aux :: (MonadFresh m) => Maybe (Var (Src t)) -> (Var (Src t) -> m (Co t a)) -> m (Co t a)
exist_aux t f = do
  v <- fresh t
  Co rc k <- f v 
  return $ Co (Lo.CExist v rc)
              (\ decode -> do t <- decode v
                              a <- k decode
                              return (t, a))

exist :: forall m t a. (MonadFresh (Var (Src t)) m, Traversable (Src t)) =>
         (Var (Src t) -> m (Co t a)) -> m (Co t (t,a))
exist f = exist_aux (Nothing :: Maybe (Var (Src t))) f

-- construct :: Var (Src t) -> (Var (Src t) -> IO (Co t a)) -> IO (Co t a)
construct t f = exist_aux (Just t) f


exist_aux_ t f = do
  -- v <- Lo.makeFresh t
  v <- undefined
  Co rc k <- f v
  return $ Co (Lo.CExist v rc) k

-- exist_ ::  (Var (Src t) -> IO (Co t a)) -> Co t a
exist_ f = exist_aux_ Nothing f

-- construct_ :: (Src t) (Var (Src t)) -> (Var (Src t) -> IO (Co t a)) -> Co t a
construct_ t f = exist_aux_ (Just t) f 
  

lift f v1 t2 = construct_ t2 $ \v2 -> f v1 v2

--------------------------------------------------------------------------
{- Equations -}
  
v1 -=- v2 = Co (Lo.CEq v1 v2) (\env -> return ())



-------------------------------------------------------------------------

inst :: MonadRef r m => TermVar -> Lo.Var (Src t) -> m (Co t [t])
inst x v = do
  witnesses <- newRef []
  return $ Co (Lo.CInstance x v witnesses)
              (\ env -> do
                    ws <- readRef witnesses
                    mapM env ws)

--------------------------------------------------------------------------

def :: TermVar -> Var (Src t) -> Co t a -> Co t a
def x v (Co rc k) = Co (Lo.CDef x v rc) k

-- solve :: Bool -> Co t a -> a
-- solve = error "solve"




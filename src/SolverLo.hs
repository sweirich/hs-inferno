{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE RankNTypes, ScopedTypeVariables #-}
{-# OPTIONS_GHC -fdefer-type-errors #-}

module SolverLo where

import Control.Monad.Except
import Control.Applicative

import Control.Monad.Reader
import Control.Monad.Catch

import Data.Array.MArray
import Control.Monad.Ref
-- import Data.IORef

import Data.Typeable

import UnifierSig
import qualified Unifier as U
import qualified Generalization as G

import Data.Map (Map)
import qualified Data.Map as Map

-- term variables
type TermVar = String

-- type schemes
type Scheme m s = G.Scheme m s

-- type variables
type Var m s = U.Variable m s
 

data RawCo m s =
    CTrue
  | CConj (RawCo m s) (RawCo m s)
  | CEq (Var m s) (Var m s)
  | CExist (Var m s) (RawCo m s)
  | CInstance TermVar (Var m s) (Ref m [Var m s])
  | CDef TermVar (Var m s) (RawCo m s)
  | CLet (Ref m (Maybe [Var m s]))
         (RawCo m s)
         [(TermVar, Var m s, Ref m (Maybe (Scheme m s)))]
         (RawCo m s)
         

data Err m s =
    Unbound TermVar
  | Unify (Var m s) (Var m s)
  | Cycle (Var m s)
    deriving (Typeable, Show)

instance (Typeable m, Typeable s) => Exception (Err m s)

type Environment m s = Map TermVar (Scheme m s)

env_lookup :: (Monad m) => TermVar -> SolverT s m (Maybe (Scheme m s))
env_lookup x = do
  env <- ask  
  return $ Map.lookup x env

env_extend :: (Monad m) => TermVar -> Scheme m s -> SolverT s m a -> SolverT s m a
env_extend x s = local (Map.insert x s)
  
type SolverT s m = ReaderT (Environment m s) m

makeFresh t = do
  U.makeFresh t G.no_rank

solve :: forall m s ra.
         (ZipM s, Typeable s, MonadFresh m, MonadRef m,
          MonadCatch m, Typeable m,
          MArray ra [U.Variable m s] m) =>
         Proxy ra -> Bool -> RawCo m s -> m ()
solve p rectypes c = do
  state <- G.initialize 
  let state' :: G.State m ra s
      state' = state
  let solve_internal :: RawCo m s -> Environment m s -> m ()
      solve_internal c env =
        case c of
         CTrue       -> return ()
         CConj c1 c2 -> solve_internal c1 env >> solve_internal c2 env
         CEq v w     -> U.unify v w
         CExist v c  -> do
           G.register state v
           solve_internal c env
         CInstance x w witness_hook -> do
           case (Map.lookup x env) of
            Nothing -> throwM $ (Unbound x :: Err m s)
            Just s  -> do
              (witnesses, v) <- G.instantiate state s
              writeRef witness_hook witnesses
              U.unify v w
         CDef x v c ->
           solve_internal c (Map.insert x (G.trivial v) env)
         CLet generalizable_hook c1 xvss c2 -> do
           G.enter state
           let vs = map (\ (_,v,_) -> v) xvss
           forM_ vs (G.register state)
           solve_internal c1 env
           (generalizable, ss) <- G.exit rectypes state vs
           env' <- foldM (\ env ((x,_,scheme_hook), s)  -> do
                                          writeRef scheme_hook (Just s)
                                          return $ Map.insert x s env) env (zip xvss ss) 
           writeRef generalizable_hook (Just generalizable)
           solve_internal c2 env'
  solve_internal c Map.empty

----------------------------------------------------------------------

-- Decoding types

-- decode_variable :: Var m (Src t) -> m Int
decode_variable x = U.desc_id x

decode_variable_as_type x =
  liftM tovar (decode_variable x)
                    
type Decoder m t = Var m (Src t) -> m t

new_decoder :: (MonadRef m, Output t) => m (Decoder m t)                 
new_decoder = U.new_acyclic_decoder

decode_scheme decode s = do
  vs <- mapM decode_variable (G.quantifiers s)
  b  <- decode (G.body s)
  return (vs, b)

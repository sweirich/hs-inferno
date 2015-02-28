{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE RankNTypes, ScopedTypeVariables #-}
{-# OPTIONS_GHC -fdefer-type-errors #-}

module SolverLo where

import Control.Monad.Except
import Control.Applicative

import Control.Monad.Reader
import Control.Monad.Catch

import Contro.Monad.Ref
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
type Scheme s = G.Scheme s

-- type variables
type Var s = U.Variable s
 

data RawCo s =
    CTrue
  | CConj (RawCo s) (RawCo s)
  | CEq (Var s) (Var s)
  | CExist (Var s) (RawCo s)
  | CInstance TermVar (Var s) (IORef [Var s])
  | CDef TermVar (Var s) (RawCo s)
  | CLet (IORef [Var s])
         (RawCo s)
         [(TermVar, Var s, IORef (Scheme s))]
         (RawCo s)
         

data Err s =
    Unbound TermVar
  | Unify (Var s) (Var s)
  | Cycle (Var s)
    deriving (Typeable, Show)

instance (Typeable s) => Exception (Err s)

type Environment s = Map TermVar (Scheme s)

env_lookup :: TermVar -> SolverM s (Maybe (Scheme s))
env_lookup x = do
  env <- ask  
  return $ Map.lookup x env

env_extend :: TermVar -> Scheme s -> SolverM s a -> SolverM s a
env_extend x s = local (Map.insert x s)
  
type SolverM s = ReaderT (Environment s) IO

makeFresh = do
  f <- U.makeFresh
  return $ \t -> f t G.no_rank

solve :: forall s. (ZipM s, Typeable s) => (G.Fresher s) -> Bool -> RawCo s -> IO ()
solve fr rectypes c = do
  state <- G.initialize fr

  let solve_internal :: RawCo s -> Environment s -> IO ()
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
            Nothing -> throwM $ (Unbound x :: Err s)
            Just s  -> do
              (witnesses, v) <- G.instantiate state s
              writeIORef witness_hook witnesses
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
                                          writeIORef scheme_hook s
                                          return $ Map.insert x s env) env (zip xvss ss) 
           writeIORef generalizable_hook generalizable
           solve_internal c2 env'
  solve_internal c Map.empty

----------------------------------------------------------------------

    
type Decoder t = Var (Src t) -> IO t

new_decoder :: Output t => IO (Decoder t)                 
new_decoder =
  U.new_acyclic_decoder


{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE RankNTypes, ScopedTypeVariables #-}
{-# OPTIONS_GHC -fdefer-type-errors #-}

module Language.Inferno.SolverLo where

import Control.Monad.Except
import Control.Applicative

import Control.Monad.Reader
import Control.Monad.Catch

import Data.Array.MArray
import Control.Monad.Ref
import Control.Monad.EqRef

import Data.Typeable
import qualified Data.Maybe as Maybe

import Language.Inferno.UnifierSig
import qualified Language.Inferno.Unifier as U
import qualified Language.Inferno.Generalization as G

import Data.Map (Map)
import qualified Data.Map as Map

import qualified Data.List as List

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
           -- variables to generalize
         (RawCo m s)
           -- constraint from RHSs
         [(TermVar, Var m s, Ref m (Maybe (Scheme m s)))]
           -- constraint abstraction???
         (RawCo m s)
           -- constraint from body


instance (Show (RawCo m s)) where
  show CTrue             = "True"
  show (CConj c1 c2)     = show c1 ++ "," ++ show c2
  show (CEq v1 v2)       = "{" ++ show v1 ++ " = " ++ show v2 ++ "}"
  show (CExist v c)      = "Ex " ++ show (U.getId v) ++ "." ++ show c
  show (CInstance x v _) = "inst " ++ x ++ "@" ++ show (U.getId v)
  show (CDef x v c)      = "(def" ++ x ++ "=" ++ show (U.getId v)
                           ++ " in " ++ show c ++ ")"
  show (CLet _ c1 [] c2) = "let0 " ++ show c1 ++ " in " ++ show c2
  show (CLet _ c1 [(x,v,_)] c2) =
    "let1 " ++ x  ++ "= \\" ++ show (U.getId v) ++ "." ++ show c1 ++ " in " ++ show c2
  show (CLet _ c1 _ c2) = "letn " ++ show c1 ++ " in " ++ show c2

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
         (ZipM s, Typeable s, MonadFresh m, MonadEqRef m, MonadIO m,
          MonadCatch m, Typeable m, Show (s (U.Variable m s)), 
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
         CEq v w     -> do
           -- vi <- U.desc_id v
           -- wi <- U.desc_id w                 
           -- liftIO $ putStrLn $ "unifying " ++ show vi ++ " and " ++ show wi 
           U.unify v w
         CExist v c  -> do
           G.register state v
           solve_internal c env
         CInstance x w witness_hook -> do
           -- the environment provides a type scheme for [x]
           case (Map.lookup x env) of
            Nothing -> throwM $ (Unbound x :: Err m s)
            Just sigma  -> do
              -- liftIO $ putStrLn $ "instantiating: " ++ show x
              (witnesses, v) <- G.instantiate state sigma
              oldw <- readRef witness_hook
              unless (null oldw) $ error "BUG: witness hook not empty"
              writeRef witness_hook witnesses
              {- forM_ witnesses (\v -> do
                       vi <- U.desc_id v
                       liftIO $ putStrLn $ "writing: " ++ show vi)
              liftIO $ putStrLn $ "unifying at inst: " ++ show (U.getId v) ++ " "
                ++ show (U.getId w) -}
              U.unify v w
         CDef x v c ->
           solve_internal c (Map.insert x (G.trivial v) env)
         CLet generalizable_hook c1 xvss c2 -> do
           G.enter state
           let vs = map (\ (_,v,_) -> v) xvss
           forM_ vs (G.register state)
           solve_internal c1 env
           (generalizable, ss) <- G.exit rectypes state vs
           env' <- foldM (\ env1 ((x,_,scheme_hook), s) -> do
                                          writeRef scheme_hook (Just s)
                                          return $ Map.insert x s env1) env
                   (zip xvss ss) 
           writeRef generalizable_hook (Just generalizable)
           solve_internal c2 env'
  solve_internal c Map.empty

----------------------------------------------------------------------

showScheme :: forall m t.
              (MonadRef m, Output t, Show t, MonadIO m) =>
              Proxy t -> Scheme m (Src t) -> m String
showScheme p s = do
  decode <- (new_decoder :: m (Decoder m t))
  (vs,b) <- decode_scheme decode s
  let vars = concat (List.intersperse " " (map show vs))
  return $ "Forall " ++ vars ++ "." ++ show b

-- Decoding types

-- decode_variable :: Var m (Src t) -> m Int
decode_variable x = do
  vi  <- U.desc_id x
  rnk <- U.rank x
  str <- U.structure x
  when (rnk == G.no_rank) $ error "internal bug in decode_variable"
  when (Maybe.isJust str) $ error $ "structure found for var " ++ show vi
  U.desc_id x

decode_variable_as_type x =
  liftM tovar (decode_variable x)
                    
type Decoder m t = Var m (Src t) -> m t

new_decoder :: (MonadIO m, MonadRef m, Output t) => m (Decoder m t)                 
new_decoder = U.new_acyclic_decoder

decode_scheme decode s = do
  vs <- mapM decode_variable (G.quantifiers s)
  b  <- decode (G.body s)
  return (vs, b)

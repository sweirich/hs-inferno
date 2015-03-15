{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE RankNTypes, ScopedTypeVariables #-}
{-# OPTIONS_GHC -fdefer-type-errors #-}

module Language.Inferno.M.SolverLo where

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
import Language.Inferno.SolverM (M)
import qualified Language.Inferno.M.Unifier as U
import qualified Language.Inferno.M.Generalization as G

import Data.Map (Map)
import qualified Data.Map as Map

import qualified Data.List as List

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
  | CInstance TermVar (Var s) (Ref M [Var s])
  | CDef TermVar (Scheme s) (RawCo s)
  | CLet Bool -- recursive let?
         (Ref M (Maybe [Var s]))
           -- ^ variables to generalize
         (RawCo s)
           -- ^ constraint from RHSs
         [(TermVar, Var s, Ref M (Maybe (Scheme s)))]
           -- ^ (multiple) term vars and their types
         (RawCo s)
           -- ^ constraint from body


instance (Show (RawCo s)) where
  show CTrue             = "True"
  show (CConj c1 c2)     = show c1 ++ "," ++ show c2
  show (CEq v1 v2)       = "{" ++ show v1 ++ " = " ++ show v2 ++ "}"
  show (CExist v c)      = "Ex " ++ show (U.getId v) ++ "." ++ show c
  show (CInstance x v _) = "inst " ++ x ++ "@" ++ show (U.getId v)
  -- TODO: add quantifiers
  show (CDef x v c)      = "(def" ++ x ++ "=" ++ show (U.getId (G.body v))
                           ++ " in " ++ show c ++ ")"
  show (CLet _ _ c1 [] c2) = "let0 " ++ show c1 ++ " in " ++ show c2
  show (CLet _ _ c1 [(x,v,_)] c2) =
    "let1 " ++ x  ++ "= \\" ++ show (U.getId v) ++ "." ++ show c1 ++ " in " ++ show c2
  show (CLet _ _ c1 _ c2) = "letn " ++ show c1 ++ " in " ++ show c2

data Err s =
    Unbound TermVar
  | Unify (Var s) (Var s)
  | Cycle (Var s)
    deriving (Typeable, Show)

instance (Typeable s) => Exception (Err s)

type Environment s = Map TermVar (Scheme s)

env_lookup :: (Monad m) => TermVar -> SolverT s m (Maybe (Scheme s))
env_lookup x = do
  env <- ask  
  return $ Map.lookup x env

env_extend :: (Monad m) => TermVar -> Scheme s -> SolverT s m a -> SolverT s m a
env_extend x s = local (Map.insert x s)
  
type SolverT s m = ReaderT (Environment s) m

makeFresh t = do
  U.makeFresh t G.no_rank

solve :: forall s.
         (ZipM s, Typeable s, Show (s (U.Variable s))) =>
          Bool -> RawCo s -> M ()
solve rectypes c = do
  state <- G.initialize 
  let state' :: G.State s
      state' = state
  let solve_internal :: RawCo s -> Environment s -> M ()
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
            Nothing -> throwM $ (Unbound x :: Err s)
            Just sigma  -> do
              -- liftIO $ putStrLn $ "instantiating: " ++ show x
              (witnesses, v) <- G.instantiate state sigma
              oldw <- readRef witness_hook
              unless (null oldw) $ error "BUG: witness hook not empty"
              writeRef witness_hook witnesses
              U.unify v w
         CDef x s c ->
           solve_internal c (Map.insert x s env)
         CLet is_rec generalizable_hook c1 xvss c2 -> do
           G.enter state
           let vs = map (\ (_,v,_) -> v) xvss               
           forM_ vs (G.register state)
           -- recursive let
           let env2 = if is_rec then
                         foldr (\ (x,v,_) -> Map.insert x (G.trivial v)) env xvss
                      else env
           solve_internal c1 env2
           (generalizable, ss) <- G.exit rectypes state vs
           env' <- foldM (\ env1 ((x,_,scheme_hook), s) -> do
                                          writeRef scheme_hook (Just s)
                                          return $ Map.insert x s env1) env
                   (zip xvss ss) 
           writeRef generalizable_hook (Just generalizable)
           solve_internal c2 env'
  solve_internal c Map.empty

----------------------------------------------------------------------

showScheme :: forall t. (Output t, Show t) =>
              Proxy t -> Scheme (Src t) -> M String
showScheme p s = do
  decode <- (new_decoder :: M (Decoder t))
  (vs,b) <- decode_scheme decode s
  let vars = concat (List.intersperse " " (map show vs))
  return $ "Forall " ++ vars ++ "." ++ show b

-- Decoding types

-- decode_variable :: Var (Src t) -> m Int
decode_variable x = do
  vi  <- U.desc_id x
  rnk <- U.rank x
  str <- U.structure x
  when (rnk == G.no_rank) $ error "internal bug in decode_variable"
  when (Maybe.isJust str) $ error $ "structure found for var " ++ show vi
  U.desc_id x

decode_variable_as_type x =
  liftM tovar (decode_variable x)
                    
type Decoder t = Var (Src t) -> M t

new_decoder :: (Output t) => M (Decoder t)                 
new_decoder = U.new_acyclic_decoder

decode_scheme decode s = do
  vs <- mapM decode_variable (G.quantifiers s)
  b  <- decode (G.body s)
  return (vs, b)

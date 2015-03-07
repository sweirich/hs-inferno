{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Language.Inferno.SolverM (M,
                                 solve,
                                 runSolverM,
                                 Foldable,
                                 Traversable,
                                 Typeable,
                                 module Language.Inferno.UnifierSig,
                                 module Language.Inferno.SolverHi) where


import Language.Inferno.UnifierSig

import Data.Foldable (Foldable(..))
import Data.Traversable (Traversable(..))
import Data.Typeable

import Control.Applicative
import Control.Monad
import Control.Monad.Trans
import Control.Monad.State
import Control.Monad.Ref
import Control.Monad.EqRef
import Control.Monad.Catch

import Data.Array.Base
import Data.Array.MArray
import Data.Array.IO

import Data.IORef

import Language.Inferno.SolverHi hiding (solve)
import qualified Language.Inferno.SolverHi as Hi
import qualified Language.Inferno.SolverLo as Lo


newtype M a = SolverM (StateT Int IO a)
   deriving (Typeable, MonadState Int, Applicative, Monad, Functor)
            
unSolverM (SolverM m) = m

solve :: (Show (Src t (Var M (Src t))),
          Output t) => Co M t a -> M a
solve = Hi.solve (Proxy :: Proxy IOArray) False

runSolverM :: M a -> IO a
runSolverM (SolverM m) = evalStateT m 0

instance MonadRef M where
  type Ref M = IORef

  readRef r    = SolverM $ readRef r
  newRef x     = SolverM $ newRef x
  writeRef r x = SolverM $ writeRef r x

instance MonadEqRef M where
  eqRef _ r1 r2  = eqRef (Proxy :: Proxy IO) r1 r2

instance MonadFresh M where
  fresh = do
    x <- get
    put (x + 1)
    return x
    
instance MonadCatch M where
  catch (SolverM m) b = SolverM $ catch m (\x -> unSolverM $ b x)

instance MonadThrow M where
  throwM e = SolverM $ throwM e

instance MonadIO M where
  liftIO m  = SolverM $ liftIO m

instance MArray IOArray a M where
  getBounds x       = SolverM $ lift $ getBounds x
  newArray x y      = SolverM $ lift $ newArray x y
  getNumElements x  = SolverM $ lift $ getNumElements x
  unsafeRead a i    = SolverM $ lift $ unsafeRead a i
  unsafeWrite a i x = SolverM $ lift $ unsafeWrite a i x 


{-
dec :: forall s. Lo.RawCo M s -> M String
dec x = do
  decode <- (Lo.new_decoder :: M (Lo.Var M s -> M String))
  let dec_internal x = 
        case x of
         Lo.CTrue -> return "True"
         Lo.CConj c1 c2 -> do
           s1 <- dec_internal c1
           s2 <- dec_internal c2
           return $ s1 ++ "," ++ s2
         Lo.CEq v1 v2 -> do
           s1 <- decode v1
           s2 <- decode v2
           return $ "{" ++ s1 ++ "=" ++ s2 ++ "}"
         Lo.CExist v c -> do
           s1 <- decode v
           s2  <- dec_internal c
           return $ "Ex " ++ s1 ++ "." ++ s2
         Lo.CInstance x v rs -> do
           s  <- decode v
           return $ "Inst " ++ x ++ "@" ++ s
         Lo.CDef x v c -> do
           s <- decode v
           s2 <- dec_internal c
           return $ "(def" ++ x ++ "=" ++ s ++ " in " ++ s2 ++ ")"
         Lo.CLet _ c1 [] c2 -> do
           s1 <- dec_internal c1
           s2 <- dec_internal c2
           return $ "let0 " ++ s1 ++ " in " ++ s2
         Lo.CLet _ c1 [(x,v,_)] c2 -> do
           s1 <- dec_internal c1
           s2 <- dec_internal c2
           s3  <- decode v
           return $ "let1 " ++ x ++ "= \\" ++ s3 ++ "." ++ s1 ++ " in " ++ s2
         Lo.CLet _ c1 xvss c2 -> do
           s1 <- dec_internal c1
           s2 <- dec_internal c2
           return $ "letn " ++ s1 ++ " in " ++ s2
           
  dec_internal x
-}

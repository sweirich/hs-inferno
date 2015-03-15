{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeFamilies #-}

{-# OPTIONS_GHC -fno-warn-warnings-deprecations #-}


-- |
-- Module      :  Control.Monad.EqRef
-- Copyright   :  (c) University of Pennsylvania 2015
--                (c) Stephanie Weirich
-- License     :  BSD-style
-- Maintainer  :  Stephanie Weirich <sweirich@cis.upenn.edu>
--
-- Stability   :  experimental
-- Portability :  non-portable

module Control.Monad.EqRef where

import Control.Monad.Ref
import Data.Typeable(Proxy(..))


import Control.Concurrent.STM (STM)
import Control.Concurrent.STM.TVar (TVar,
                                    newTVar,
                                    readTVar,
                                    writeTVar)
import Control.Monad.ST (ST)
import Control.Monad.Trans.Cont (ContT)
import Control.Monad.Trans.Error (ErrorT, Error)
#if MIN_VERSION_transformers(0,4,0)
import Control.Monad.Trans.Except (ExceptT)
#endif /* MIN_VERSION_transformers(0,4,0) */
import Control.Monad.Trans.Identity (IdentityT)
import Control.Monad.Trans.List (ListT)
import Control.Monad.Trans.Maybe (MaybeT)
import Control.Monad.Trans.Reader (ReaderT)
import Control.Monad.Trans.State.Lazy as Lazy (StateT)
import Control.Monad.Trans.State.Strict as Strict (StateT)
import Control.Monad.Trans.Writer.Lazy as Lazy (WriterT)
import Control.Monad.Trans.Writer.Strict as Strict (WriterT)
import Control.Monad.Trans.Class (lift)
import Data.IORef (IORef,
#if MIN_VERSION_base(4,6,0)
                   atomicModifyIORef',
                   modifyIORef',
#endif /* MIN_VERSION_base(4,6,0) */
                   atomicModifyIORef,
                   modifyIORef,
                   newIORef,
                   readIORef,
                   writeIORef)
import Data.Monoid (Monoid)
import Data.STRef (STRef,
#if MIN_VERSION_base(4,6,0)
                   modifySTRef',
#endif /* MIN_VERSION_base(4,6,0) */
                   modifySTRef,
                   newSTRef,
                   readSTRef,
                   writeSTRef)


class MonadRef m => MonadEqRef m where
  -- | Equality for refs, with a proxy argument so that it
  -- can be called unambiguously
  eqRef     :: Proxy m -> Ref m a -> Ref m a -> Bool


instance MonadEqRef (ST s) where
  eqRef _ = (==)
instance MonadEqRef IO where
  eqRef _ = (==)

instance MonadEqRef STM where
  eqRef _ = (==)

instance MonadEqRef m => MonadEqRef (ContT r m) where
  eqRef p  r1 r2 = eqRef (Proxy :: Proxy m) r1 r2

instance (Error e, MonadEqRef m) => MonadEqRef (ErrorT e m) where
  eqRef p  r1 r2 = eqRef (Proxy :: Proxy m) r1 r2

#if MIN_VERSION_transformers(0,4,0)
instance (MonadEqRef m) => MonadEqRef (ExceptT e m) where
   eqRef  _ r1 r2 = eqRef (Proxy :: Proxy m) r1 r2    
#endif /* MIN_VERSION_transformers(0,4,0) */

instance MonadEqRef m => MonadEqRef (IdentityT m) where
   eqRef _  r1 r2 = eqRef (Proxy :: Proxy m) r1 r2

instance MonadEqRef m => MonadEqRef (ListT m) where
   eqRef _  r1 r2 = eqRef (Proxy :: Proxy m) r1 r2

instance MonadEqRef m => MonadEqRef (MaybeT m) where
   eqRef _  r1 r2 = eqRef (Proxy :: Proxy m) r1 r2

instance MonadEqRef m => MonadEqRef (ReaderT r m) where
   eqRef _  r1 r2 = eqRef (Proxy :: Proxy m) r1 r2


instance MonadEqRef m => MonadEqRef (Lazy.StateT s m) where
    eqRef  _ r1 r2 = eqRef (Proxy :: Proxy m) r1 r2
    
instance MonadEqRef m => MonadEqRef (Strict.StateT s m) where
    eqRef  _ r1 r2 = eqRef (Proxy :: Proxy m) r1 r2
    
instance (Monoid w, MonadEqRef m) => MonadEqRef (Lazy.WriterT w m) where
    eqRef  _ r1 r2 = eqRef (Proxy :: Proxy m) r1 r2
    
instance (Monoid w, MonadEqRef m) => MonadEqRef (Strict.WriterT w m) where
    eqRef  _ r1 r2 = eqRef (Proxy :: Proxy m) r1 r2

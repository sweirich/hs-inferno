{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}

module Language.Inferno.TRef (TRef,
             newTRef,
             readTRef,
             TransM,
             writeTRef,
             tentatively, indubitably) where


import Control.Monad.Catch
import Control.Monad.Reader

import Data.Maybe
import Control.Applicative

import Data.Typeable


import Control.Monad.Ref
import Control.Monad.EqRef

{-
   Every cell records both its current (possibly uncommitted) value
   and its last committed value. A cell is considered stable when
   these two values are (physically) equal, and unstable otherwise.
-}

type TransM a m = ReaderT (Ref m [TRef m a]) m 

data TRef m a = TRef {
  current   :: Ref m a,
  committed :: Ref m a
} 

instance (MonadEqRef m) => Eq (TRef m a) where
  tr1 == tr2 = eqRef' (current tr1) (current tr2) &&
               eqRef' (committed tr1) (committed tr2) where
     eqRef' = eqRef (Proxy :: Proxy m)
               

 
-- TRefs are not created after the beginning of a transaction 

-- newTRef :: MonadRef r m  => a -> m (TRef r a)
newTRef v = do
  cur <- newRef v
  com <- newRef v
  return $ TRef cur com

readTRef :: MonadRef m => TRef m a -> m a 
readTRef cell = readRef (current cell)

writeTRef :: (MonadRef m, Eq a) =>  TRef m a -> a -> TransM a m ()
writeTRef cell v = do
  cur <- readRef (current cell)
  unless (v == cur) $ do
    com <- readRef (committed cell)
    when (cur == com) $ do
      stack <- ask
      transactions <- readRef stack
      writeRef stack (cell : transactions)
    writeRef (current cell) v

commit :: (MonadRef m) => TRef m a -> m ()
commit cell = do
  cur <- readRef (current cell)
  writeRef (committed cell) cur

rollback :: (MonadRef m) => TRef m a -> m ()
rollback cell = do
  com <- readRef (committed cell)
  writeRef (current cell) com
    
tentatively :: forall a b e m r . (MonadCatch m, MonadRef m, Eq a, Exception e)
               => Proxy e -> TransM a m b -> m b
tentatively _ f = do
  stack <- newRef []
  indubitably f 
{-  (do result <- runReaderT f stack
      transactions <- readRef stack
      forM_ transactions commit
      return result) -}
    `catch` \(e :: e) -> do
      transactions <- readRef stack
      forM_ transactions rollback
      throwM e
    

indubitably :: forall a b m r . (MonadRef m) => TransM a m b -> m b
indubitably f = do
  stack <- newRef []
  result <- runReaderT f stack
  transactions <- readRef stack
  forM_ transactions commit
  return result

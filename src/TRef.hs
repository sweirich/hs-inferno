{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE ScopedTypeVariables #-}

module TRef where

import Data.IORef
import Control.Monad.Catch
import Control.Monad.Reader

import Data.Maybe
import Control.Applicative

import Data.Typeable



-- TODO:
--  * use Control.Monad.Ref to make this file work for both ST and IO

{-
Every cell records both its current (possibly uncommitted) value
   and its last committed value. A cell is considered stable when
   these two values are (physically) equal, and unstable otherwise.
-}

type TransM a = ReaderT (IORef [TRef a]) IO

data TRef a = TRef {
  current   :: IORef a,
  committed :: IORef a
} deriving (Eq)


-- TRefs are not created after the beginning of a transaction 

newTRefIO ::  a -> IO (TRef a)
newTRefIO v = do
  cur <- newIORef v
  com <- newIORef v
  return $ TRef cur com

readTRefIO :: TRef a -> IO a 
readTRefIO cell = readIORef (current cell)

writeTRef :: Eq a => TRef a -> a -> TransM a ()
writeTRef cell v = do
  cur <- liftIO $ readIORef (current cell)
  unless (v == cur) $ do
    com <- liftIO $ readIORef (committed cell)
    when (cur == com) $ do
      stack <- ask
      transactions <- liftIO $ readIORef stack
      liftIO $ writeIORef stack (cell : transactions)
    liftIO $ writeIORef (current cell) v

commit cell = do
  cur <- readIORef (current cell)
  writeIORef (committed cell) cur

rollback cell = do
  com <- readIORef (committed cell)
  writeIORef (current cell) com
    
tentatively :: forall a b e. (Eq a, Exception e) => Proxy e -> TransM a b -> IO b
tentatively _ f = do
  stack <- newIORef []
  (do result <- runReaderT f stack
      transactions <- readIORef stack
      forM_ transactions commit
      return result)
    `catch` \(e :: e) -> do
      transactions <- readIORef stack
      forM_ transactions rollback
      throwM e
    


{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}

-- a version in specialized to the M monad

module Language.Inferno.M.TRef (TRef,
             newTRef,
             readTRef,
             TransM,
             writeTRef,
             tentatively, indubitably) where

import Language.Inferno.SolverM

import Control.Monad.Catch
import Control.Monad.Reader

import Data.Maybe
import Control.Applicative

import Data.Typeable

import Control.Monad.Ref

-- import Control.Monad.EqRef

{-
   Every cell records both its current (possibly uncommitted) value
   and its last committed value. A cell is considered stable when
   these two values are (physically) equal, and unstable otherwise.
-}

type TransM a = ReaderT (Ref M [TRef a]) M 

data TRef a = TRef {
  current   :: Ref M a,
  committed :: Ref M a
} deriving (Eq)

 
-- TRefs are not created after the beginning of a transaction 

-- newTRef ::  a -> M (TRef a)
newTRef v = do
  cur <- newRef v
  com <- newRef v
  return $ TRef cur com

readTRef :: TRef a -> M a 
readTRef cell = readRef (current cell)

writeTRef :: (Eq a) =>  TRef a -> a -> TransM a ()
writeTRef cell v = do
  cur <- readRef (current cell)
  unless (v == cur) $ do
    com <- readRef (committed cell)
    when (cur == com) $ do
      stack <- ask
      transactions <- readRef stack
      writeRef stack (cell : transactions)
    writeRef (current cell) v

commit :: TRef a -> M ()
commit cell = do
  cur <- readRef (current cell)
  writeRef (committed cell) cur

rollback :: TRef a -> M ()
rollback cell = do
  com <- readRef (committed cell)
  writeRef (current cell) com
    
tentatively :: forall a b e . (Eq a, Exception e)
               => Proxy e -> TransM a b -> M b
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
    

indubitably :: TransM a b -> M b
indubitably f = do
  stack <- newRef []
  result <- runReaderT f stack
  transactions <- readRef stack
  forM_ transactions commit
  return result

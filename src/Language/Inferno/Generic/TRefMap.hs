{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

module Language.Inferno.TRefMap where

-- A mutable map data structure for TRefs


-- Note: see Data.HashTable interface

import Prelude hiding (lookup)
import qualified Prelude (lookup)

import Data.Maybe
import Control.Monad
import Control.Monad.Ref

data TRefMap m a v = TRefMap { table :: (Ref m) [(a,v)], 
                               eqv   :: a -> a -> m Bool }

new :: MonadRef m => (a -> a -> m Bool) -> m (TRefMap m a v)
new eqv = do
  r <- newRef []
  return (TRefMap r eqv)

lookup :: MonadRef m => (TRefMap m a v) -> a -> m (Maybe v)
lookup m a1 = do
  mr <- readRef (table m)
  let loop [] = return Nothing
      loop ((a2,v):assocs) = do
        b <- eqv m a1 a2
        if b then return (Just v) else loop assocs
  loop mr

member m r = 
  liftM isJust $ lookup m r

insert m r v = do
  mr <- readRef (table m)
  writeRef (table m) ((r,v): mr)



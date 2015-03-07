{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

module Language.Inferno.VarMap where

-- A mutable map data structure for Unifier Variables

-- TODO: change this to Hashtables
-- Note: see Data.HashTable interface

import Prelude hiding (lookup)
import qualified Prelude (lookup)

import Data.Maybe
import Control.Monad
import Control.Monad.Ref

data VarMap m v = VarMap { table :: (Ref m) [(Int,v)] }

new :: MonadRef m =>  m (VarMap m v)
new = do
  r <- newRef []
  return (VarMap r)

lookup :: MonadRef m => (VarMap m v) -> Int -> m (Maybe v)
lookup m a1 = do
  mr <- readRef (table m)
  let loop [] = return Nothing
      loop ((a2,v):assocs) = do
        if a1 == a2 then return (Just v) else loop assocs
  loop mr

member m r = 
  liftM isJust $ lookup m r

insert m r v = do
  mr <- readRef (table m)
  writeRef (table m) ((r,v): mr)



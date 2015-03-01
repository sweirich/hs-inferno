{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

module TRefMap where

-- A mutable map data structure for TRefs


-- Note: see Data.HashTable interface

import Prelude hiding (lookup)
import qualified Prelude (lookup)

import Data.Maybe

-- import Data.IORef

import Control.Monad
import Control.Monad.Ref

type TRefMap m a v = (Ref m) [(a,v)]

new :: MonadRef m => m (TRefMap m a v)
new = do
  r <- newRef []
  return r

lookup m r = do
  mr <- readRef m
  return $ Prelude.lookup r mr

member m r = 
  liftM isJust $ lookup m r

insert m r v = do
  mr <- readRef m
  writeRef m ((r,v): mr)



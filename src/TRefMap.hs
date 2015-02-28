{-# LANGUAGE NoImplicitPrelude #-}

module TRefMap where

-- A mutable map data structure for TRefs


-- Note: see Data.HashTable interface

import Prelude hiding (lookup)
import qualified Prelude (lookup)

import Data.Maybe
import Control.Applicative

import Data.IORef


-- TODO: use Control.Monad.Ref to make this file work for both ST and IO
--       add a creation time id so that we can hash these puppies

type TRefMap a v = IORef [(a,v)]

new = do
  r <- newIORef []
  return r

lookup m r = do
  mr <- readIORef m
  return $ Prelude.lookup r mr

member m r = 
  isJust <$> lookup m r

insert m r v = do
  mr <- readIORef m
  writeIORef m ((r,v): mr)



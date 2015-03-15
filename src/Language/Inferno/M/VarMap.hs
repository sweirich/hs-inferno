{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}

module Language.Inferno.M.VarMap where

-- A mutable map data structure for Unifier Variables

-- TODO: change this to Hashtables
-- Note: see Data.HashTable interface

import Prelude hiding (lookup)
import qualified Prelude (lookup)

import Data.Maybe
import Control.Monad
import Control.Monad.Trans
import Control.Monad.Ref

import Language.Inferno.SolverM

import qualified Data.HashTable.IO as H

data VarMap v = VarMap { table :: H.BasicHashTable Int v }

new :: M (VarMap v)
new = liftIO $ do
  r <- H.new
  return (VarMap r)

lookup :: (VarMap v) -> Int -> M (Maybe v)
lookup (VarMap m) a1 = liftIO (H.lookup m a1)
{-
              do
  mr <- readRef (table m)
  let loop [] = return Nothing
      loop ((a2,v):assocs) = do
        if a1 == a2 then return (Just v) else loop assocs
  loop mr
-}

member m r = 
  liftM isJust $ lookup m r

insert (VarMap m) r v = liftIO $ H.insert m r v

{-
  do
  mr <- readRef (table m)
  writeRef (table m) ((r,v): mr)
-}


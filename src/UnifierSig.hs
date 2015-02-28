{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
module UnifierSig where


import Data.Foldable (Foldable(..))
import Data.Traversable (Traversable(..))

import Data.Typeable
import Control.Monad.Catch


class (Monad m) => MonadFresh m where
  fresh :: m Int


-- What ever type structure we use must be an instance
-- of the ZipM class
data ZipError a = ZipError a a
   deriving (Show, Typeable, Eq)
instance (Show a, Typeable a) => Exception (ZipError a)

class (Typeable t, Traversable t, Foldable t) => ZipM t where
  zipM  :: (Typeable a, Show a, MonadThrow m) =>
      (a -> a -> m b) -> t a -> t a -> m (t b)
      
  zipM_ :: (Typeable a, Show a, MonadThrow m) =>
      (a -> a -> m ()) -> t a -> t a -> m ()


-- The output of the unifier must be an instance of this class.
-- TODO: rename these members
class (Traversable (Src t)) => Output t where
  type Src t :: * -> *
  tovar  :: Int -> t
  struc  :: (Src t) t -> t

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
module Language.Inferno.UnifierSig where


import Data.Foldable (Foldable(..))
import Data.Traversable (Traversable(..))

import Data.Typeable
import Control.Monad.Catch

import Text.PrettyPrint (Doc)
import qualified Text.PrettyPrint as PP


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

{-
-- From Conor's email
-- https://mail.haskell.org/pipermail/libraries/2012-July/018249.html
class Functor f => HalfZippable f where
    -- Conor's operation
    halfZip :: f a -> f b -> Maybe (f (a, b))

    -- other versions
    halfZipWith :: (a -> b -> c) -> f a -> f b -> Maybe (f c)

    halfZipWith_ :: (a -> b -> ()) -> f a -> f b -> Bool

    -- other versions
    halfZipWithM  :: (Monad m) =>
                     (a -> b -> m c) -> f a -> f b -> m (Maybe (f c))
    halfZipWithM_ :: (Monad m) =>
                     (a -> b -> m ()) -> f a -> f b -> m Bool

-}    


class Pretty a where
  ppPrec :: Int -> a -> Doc
  
  prec   :: a -> Int
  prec   _ = 0
  
  ppList :: [a] -> Doc
  ppList l = PP.brackets (PP.cat (PP.punctuate (PP.text ",") (map pp l)))

  pp     :: a -> Doc
  pp     = ppPrec 11

-- The output of the unifier must be an instance of this class.
-- TODO: rename these members
class (Typeable t,
       Show t,
       ZipM (Src t), 
       Traversable (Src t)) => Output t where
  type Src t :: * -> *
  tovar  :: Int -> t
  struc  :: (Src t) t -> t

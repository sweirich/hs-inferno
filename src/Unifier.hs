{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -fdefer-type-errors #-}

module Unifier where


import Control.Monad 
import Control.Monad.IO.Class
import Control.Applicative
import Data.Monoid

import Data.Foldable (Foldable(..))
import qualified Data.Foldable as F
import Data.Traversable (Traversable(..))
import qualified Data.Traversable as T

import Data.Typeable
import Control.Monad.Catch
import Control.Monad.Ref
-- import Data.IORef

import UnifierSig

import TRef
import qualified TRefMap
import qualified TUnionFind as UF


----------------------------------------------------------------

{- The data structure maintained by the unifier is as follows. -}

{-
   A unifier variable is a point of the union-find algorithm.
   We also keep an identifier with it for hashing.
-}

data Variable m s = Variable
                  { getPoint :: UF.Point m (Descriptor m s),
                    getId    :: Int }
  deriving (Typeable)



{- Every equivalence class carries a descriptor which contains
   the following information. -}

{- Some of the fields below are mutable, because our client sometimes
   needs to update them. However, this is never done by the unifier
   itself, hence never done during unification. The unification algorithm
   is transactional: it writes only [TVars]s, so that all changes can be
   rolled back if unification fails.
-}

data Descriptor m s = Descriptor {
    descId    :: Int,
    descStruc :: (Ref m) (Maybe (s (Variable m s))),
    descRank  :: (Ref m) Int
  } deriving (Typeable)

instance Eq (Variable m s) where
  v1 == v2 = (getId v1) == (getId v2)
instance Eq (Descriptor m s) where
  d1 == d2 = (descId d1) == (descId d2)

instance Show (Variable r s) where
  show x = "V:" ++ (show (getId x))
instance Show (Descriptor r s) where
  show d = "D:" ++  (show (descId d))

data Err r s = Unify (Variable r s) (Variable r s)
             | Cycle (Variable r s)
   deriving (Typeable, Show)
            
instance (Typeable s, Typeable r) => Exception (Err r s)

-- accessors
desc_id v = liftM descId $ UF.find (getPoint v)

structure v = do
  s <- liftM descStruc $ UF.find (getPoint v)
  readRef s 

set_structure v x = do
  s <- liftM descStruc $ UF.find (getPoint v)
  writeRef s x

rank v = do
   r <- liftM descRank $ UF.find (getPoint v)
   readRef r

set_rank v x = do
  r <- liftM descRank $ UF.find (getPoint v)
  writeRef r x

adjust_rank v k = do
  r <- liftM descRank $ UF.find (getPoint v)
  rank <- readRef r
  when (k < rank) (writeRef r k)

{- ----------------------------------------------------------------- -}

{-
postincrement r = do
  v <- readIORef r
  writeIORef r (v + 1)
  return v
-}

{- ----------------------------------------------------------------- -}


makeFresh :: (MonadRef m, MonadFresh m) =>
             Maybe (s (Variable m s)) -> Int -> m (Variable m s)
makeFresh ms rank = do
     id  <- fresh
     str <- newRef ms
     rnk <- newRef rank
     point <- UF.fresh $ Descriptor id str rnk
     return $ Variable point id


{- The internal function [unify t v1 v2] equates the variables [v1] and
   [v2] and propagates the consequences of this equation until an
   inconsistency is found or a solved form is reached. In the former
   case, [ZipError] is raised.  -}

unify_internal v1 v2 =
  UF.union unify_descriptors (getPoint v1) (getPoint v2)


unify_descriptors desc1 desc2 = do
  s1 <- readRef (descStruc desc1)
  s2 <- readRef (descStruc desc2)
  struc <- unify_structures s1 s2
  new_struc <- newRef struc
  r1 <- readRef (descRank desc1)
  r2 <- readRef (descRank desc2)
  new_rank <- newRef (min r1 r2)
  return $
                Descriptor
                (descId desc1)
                new_struc
                new_rank

unify_structures structure1 structure2 =
  case (structure1, structure2) of
    (Just s1, Just s2) -> do _ <- zipM unify_internal s1 s2
                             return (Just s1)
    (Just s , Nothing) -> return (Just s)
    (Nothing, Just s ) -> return (Just s)
    (Nothing, Nothing) -> return Nothing


unify :: forall r m s. (Typeable m, MonadRef m, MonadCatch m, ZipM s)
         => Variable m s -> Variable m s -> m ()
unify v1 v2 = do
  tentatively (Proxy :: Proxy (Err m s))
    (unify_internal v1 v2)
    `catch` (\(e :: Err m s) ->
              throwM (Unify v1 v2))
  
    

equivalent
  :: (MonadRef m) => Variable m a -> Variable m a -> m Bool
equivalent v1 v2 = if (getId v1) == (getId v2)
                   then return True
                   else UF.equivalent (getPoint v1) (getPoint v2)

-- is_representative :: (MonadRef m) => Variable m s -> m Bool
is_representative v = UF.is_representative (getPoint v)

 ----------------------------------------------------------------- 

{- The occurs check, which detects cycles in the graph, cannot be
   defined as an instance of the cyclic decoder, for several reasons. For
   one thing, the cyclic decoder is inefficient, as it does not (cannot)
   mark the nodes that have been visited. Furthermore, the occurs check
   explores only the young generation, whereas the decoders explore
   everything. -}

-- new_occurs_check :: (Variable -> Bool) -> Variable -> M ()
new_occurs_check is_young v = do
  table <- TRefMap.new
  let -- traverse :: Variable s -> IO ()
      traverse v = do
        b <- is_young v
        when b $ do
          mb <- TRefMap.lookup table v
          case mb of
            Just visited ->
              when (not visited) $
                 -- This node is in the table, but has not been fully
                 -- visited. Hence, it is being visited. A cycle has
                 -- been found.
                 throwM (Cycle v)
            Nothing -> do
              -- Mark this variable as being visited
              TRefMap.insert table v False
              -- Visit its successors.
              str <- structure v
              case str of
                 Just x  -> F.mapM_ traverse x
                 Nothing -> return ()
              TRefMap.insert table v True
  traverse v          


-----------------------------------------------------------------
-- decoding  


new_acyclic_decoder :: forall t m.
                       (MonadRef m, Output t) => m (Variable m (Src t) -> m t)
new_acyclic_decoder = do
  table <- TRefMap.new
  
  let decode :: Variable m (Src t) -> m t
      decode v = do
        mv <- TRefMap.lookup table v
        case mv of
         Just a  -> return a
         Nothing -> do
           ms <- structure v
           a <- case ms of
                    Nothing -> do
                      i <- desc_id v
                      return $ tovar i
                    Just t  -> liftM struc (T.mapM decode t)
           TRefMap.insert table v a
           return a
          
  return $ decode
              
  
  
 

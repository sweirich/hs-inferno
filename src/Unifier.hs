{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveDataTypeable #-}
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

import Data.IORef

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

data Variable s = Variable
                  { getPoint :: UF.Point (Descriptor s),
                    getId    :: Int }
  deriving (Show, Eq, Typeable)


{- Every equivalence class carries a descriptor which contains
   the following information. -}

{- Some of the fields below are mutable, because our client sometimes
   needs to update them. However, this is never done by the unifier
   itself, hence never done during unification. The unification algorithm
   is transactional: it writes only [TVars]s, so that all changes can be
   rolled back if unification fails.
-}

data Descriptor s = Descriptor {
    descId    :: Int,
    descStruc :: IORef (Maybe (s (Variable s))),
    descRank  :: IORef Int
  } deriving (Eq, Typeable)

instance Show (Descriptor s) where
  show d = show (descId d)

data Err s = Unify (Variable s) (Variable s)
           | Cycle (Variable s)
   deriving (Typeable, Show)
instance Typeable s => Exception (Err s)

-- accessors
desc_id v = descId <$> UF.find (getPoint v)

structure v = do
  s <- descStruc <$> UF.find (getPoint v)
  readIORef s 

set_structure v x = do
  s <- descStruc <$> UF.find (getPoint v)
  writeIORef s x

rank v = do
   r <- descRank <$> UF.find (getPoint v)
   readIORef r

set_rank v x = do
  r <- descRank <$> UF.find (getPoint v)
  writeIORef r x

adjust_rank v k = do
  r <- descRank <$> UF.find (getPoint v)
  rank <- readIORef r
  when (k < rank) (writeIORef r k)

{- ----------------------------------------------------------------- -}

postincrement r = do
  v <- readIORef r
  writeIORef r (v + 1)
  return v

{- ----------------------------------------------------------------- -}


makeFresh :: MonadFresh m => s (Variable s) -> Int -> m (Variable s)
makeFresh structure rank = do
     id  <- fresh
     str <- newIORef structure
     rnk <- newIORef rank
     point <- UF.fresh $ Descriptor id str rnk
     return $ Variable id point


{- The internal function [unify t v1 v2] equates the variables [v1] and
   [v2] and propagates the consequences of this equation until an
   inconsistency is found or a solved form is reached. In the former
   case, [ZipError] is raised.  -}

unify_internal v1 v2 =
  UF.union unify_descriptors (getPoint v1) (getPoint v2)

-- unify_descriptors :: Descriptor s -> Descriptor s -> TransM (UF.Link Descriptor) Descriptor
unify_descriptors desc1 desc2 = do
  s1 <- liftIO $ readIORef (descStruc desc1)
  s2 <- liftIO $ readIORef (descStruc desc2)
  struc <- unify_structures s1 s2
  liftIO $ do new_struc <- newIORef struc
              r1 <- readIORef (descRank desc1)
              r2 <- readIORef (descRank desc2)
              new_rank <- newIORef (min r1 r2)
              return $
                Descriptor
                (descId desc1)
                new_struc
                new_rank

{-
unify_structures :: (Maybe (Structure Variable))
                    -> Maybe (Structure Variable)
                    -> TransM (UF.Link Descriptor)
                              (Maybe (Structure Variable))
-}
unify_structures structure1 structure2 =
  case (structure1, structure2) of
    (Just s1, Just s2) -> do _ <- zipM unify_internal s1 s2
                             return (Just s1)
    (Just s , Nothing) -> return (Just s)
    (Nothing, Just s ) -> return (Just s)
    (Nothing, Nothing) -> return Nothing


unify :: forall s. ZipM s => Variable s -> Variable s -> IO ()
unify v1 v2 = do
  tentatively (Proxy :: Proxy (Err s))
    (unify_internal v1 v2)
    `catch` (\(e :: Err s) ->
              throwM (Unify v1 v2))
  
    
-- equivalent :: Variable -> Variable -> M Bool
equivalent = UF.equivalent

-- is_representative :: Variable -> M Bool
is_representative = UF.is_representative

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
      traverse v = 
        when (is_young v) $ do
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


new_acyclic_decoder :: forall t. (Output t) => IO (Variable (Src t) -> IO t)
new_acyclic_decoder = do
  table <- TRefMap.new
  
  let decode :: Variable (Src t) -> IO t
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
              
  
  
 

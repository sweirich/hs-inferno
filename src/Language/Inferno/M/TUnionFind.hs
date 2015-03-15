{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# OPTIONS_GHC -funbox-strict-fields #-}

-- TODO: use a persistant data structure
-- http://jng.imagine27.com/index.php/2012-08-22-144618_purely-functional-data-structures-algorithms-union-find-haskell.html
-- Or Conchon / Filliatre: A persistent Union-Find Data structure, ML Workshop 2007

module Language.Inferno.M.TUnionFind (Point,
                   fresh,
                   repr,
                   reprT,
                   find,
                   union,
                   equivalent,
                   is_representative) where

{- This module implements a simple and efficient union/find algorithm.
    See Robert E. Tarjan, ``Efficiency of a Good But Not Linear Set
    Union Algorithm'', JACM 22(2), 1975. -}

{- This module implements a transactional variant of the union-find
   algorithm. It uses transactional references instead of ordinary
   references, so that a series of operations performed within a
   transaction can be either committed or rolled back. -}

{- See [UnionFind] for comparison. The differences are:
   - we use [TRef] instead of [IORef];
   - [find] does not perform path compression, so as to avoid
     requiring TransM;
   - [union] is in TransM -}


import Language.Inferno.SolverM (M)
import Language.Inferno.M.TRef


import Control.Applicative
import Control.Monad (when, liftM, liftM2)

import Control.Monad.Trans
import Control.Monad.Ref
import Control.Monad.EqRef

import Data.Typeable



newtype Point a =
     Point { unPoint :: TRef (Link a) }
     deriving (Typeable, Eq)


data Link a =
     Info { weight :: {-# UNPACK #-} !Int, descriptor :: a }
   | Link {-# UNPACK #-} !(Point a)
     deriving (Eq)
     -- ^ Pointer to some other element of the equivalence class.


{-
showIO (Point r p) = do
  l <- readTRef p
  case l of
    Info weight desc -> return $ show desc
    Link q -> showIO q

instance Show a => Show (Point r r a) where
  show = unsafePerformIO . showIO
-}


readPoint (Point p)  = readTRef p
writePoint (Point p) = writeTRef p


-- [fresh desc] creates a fresh point and returns it. It forms an
-- equivalence class of its own, whose descriptor is [desc]. 
fresh ::  a -> M (Point a)
fresh desc = do
  r <- newTRef Info {weight=1, descriptor=desc}
  return (Point r)

-- | /O(1)/. @repr point@ returns the representative point of
-- @point@'s equivalence class.
--
-- This version of [repr] does not perform path compression. Thus, it can be
--   used outside a transaction. 
repr :: Point a -> M (Point a)
repr point@(Point ref) = do
  link <- readTRef ref
  case link of
   Link point' -> repr point'
   Info _ _ -> return point
   
-- Return the descriptor associated with the argument's
-- equivalence class.
-- Again, this does not perform path compression.
find :: Point a -> M a
find point = do
  link <- readTRef (unPoint point)
  case link of
   Info _ desc -> return desc
   Link point' -> do
     link' <- readTRef (unPoint point')
     case link' of
       Info _ desc -> return desc
       Link _ -> 
          find =<< repr point

-- @reprT point@ returns the representative point of
-- @point@'s equivalence class.
--       
-- This version of [repr] performs path compression and
--   must be used within a transaction.
reprT :: (Eq a) => Point a -> TransM (Link a) (Point a)
reprT point = do
  link <- lift $ readPoint point
  case link of
   Link point' -> do
     point'' <- reprT point'
     when (point'' /= point') $ do
       ref' <- lift $ readPoint point'
       writePoint point ref'
     return point''
   Info _ _ -> return point


{- [union f point1 point2] merges the equivalence classes associated
    with [point1] and [point2] into a single class. Then, (and only
    then,) it sets the descriptor of this class to the one produced by
    applying the function [f] to the descriptors of the two original
    classes. It has no effect if [point1] and [point2] are already in
    the same equivalence class.

    The fact that [point1] and [point2] do not originally belong to the
    same class guarantees that we do not create a cycle in the graph.

    The weights are used to determine whether [point1] should be made
    to point to [point2], or vice-versa. By making the representative
    of the smaller class point to that of the larger class, we
    guarantee that paths remain of logarithmic length (not accounting
    for path compression, which makes them yet smaller).  -}

union f p1 p2 = do
  point1 <- reprT p1
  point2 <- reprT p2 
  when (point1 /= point2) $ do
    (Info w1 desc1) <- lift $ readPoint point1
    (Info w2 desc2) <- lift $ readPoint point2
    ds <- f desc1 desc2
    if w1 >= w2 then do
       writePoint point2 (Link point1)
       writePoint point1 (Info (w1 + w2) ds)
    else do
       writePoint point1 (Link point2)
       writePoint point2 (Info (w1 + w2) ds)
 
    
equivalent p1 p2 = do 
   r1 <- repr p1
   r2 <- repr p2
   return $ r1 == r2

is_representative point = do
  l1 <- readTRef (unPoint point)
  case l1 of
   Link _ -> return False
   Info _ _ -> return True



-- A test!
test :: M ()
test = do
  a <- fresh "a"
  b <- fresh "b"
  c <- fresh "c"
  d <- fresh "d"
  indubitably $ do
    union (\x y -> return x) a b
    union (\x y -> return x) b d
  b1 <- equivalent a b
  liftIO $ print b1
  b2 <- equivalent b c
  liftIO $ print (not b2)
  b3 <- equivalent c d
  liftIO $ print (not b3)
  b4 <- equivalent a d
  liftIO $ print b4

{-
prop_uf sets k =
  let num = length sets in
  forM [1 .. k] $ do
      j <-
-}

module UnionFind (Point,
                  fresh,
                  repr,
                  find,
                  union,
                  equivalent,
                  is_representative) where

{- This module implements a simple and efficient union/find algorithm.
    See Robert E. Tarjan, ``Efficiency of a Good But Not Linear Set
    Union Algorithm'', JACM 22(2), 1975. -}

import Data.IORef

import Control.Applicative
import Control.Monad

{-
    The abstraction defined by this module is a set of points,
    partitioned into equivalence classes. With each equivalence class,
    a piece of information, of abstract type [a], is associated; we
    call it a descriptor.

    A point is implemented as a cell, whose (mutable) contents consist
    of a single link to either information about the equivalence class,
    or another point. Thus, points form a graph, which must be acyclic,
    and whose connected components are the equivalence classes. In
    every equivalence class, exactly one point has no outgoing edge,
    and carries information about the class instead. It is the class's
    representative element.

    Information about a class consists of an integer weight (the number
    of elements in the class) and of the class's descriptor.
-}

newtype Point a = Point { unPoint :: IORef (Link a) } deriving (Eq)

readPoint (Point p) = readIORef p
writePoint (Point p) x = writeIORef p x

data Link a =
     Info { weight :: Int, descriptor :: a }
   | Link (Point a)
     deriving (Eq)

{-  [fresh desc] creates a fresh point and returns it. It forms an
    equivalence class of its own, whose descriptor is [desc]. -}
fresh desc = do
  r <- newIORef (Info 1 desc)
  return (Point r)

{- [repr point] returns the representative element of [point]'s
    equivalence class. It is found by starting at [point] and following
    the links. For efficiency, the function performs path compression
    at the same time.  -}

repr :: Point a -> IO (Point a)
repr point@(Point ref) = do
  link <- readIORef ref
  case link of
   Link point' -> do
     point'' <- repr point'
     when (point'' /= point') $ do
 	{- [point''] is [point']'s representative element. Because we just
	   invoked [repr point'], [!point'] must be [Link point'']. We
	   write this value into [point], performing path compression.
           Note that we do not perform memory allocation. -}
       ref' <- readPoint point'
       writePoint point ref'
     return point''
   Info _ _ -> return point

find :: Point a -> IO a
find point = do
  {- By not calling [repr] immediately, we optimize the common cases
     where the path starting at [point] has length 0 or 1, at the
     expense of the general case.  -}
  
  link <- readPoint point
  case link of
   Info _ desc -> return desc
   Link point' -> do
     link' <- readPoint point'
     case link' of
       Info _ desc -> return desc
       Link _ -> 
          find =<< repr point

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
  point1 <- repr p1
  point2 <- repr p2 
  when (point1 == point2) $ do
    l1 <- readPoint point1
    l2 <- readPoint point2
    case (l1,l2) of
      (Info weight1 desc1, Info weight2 desc2) -> do
        if weight1 >= weight2 then do
          writePoint point2 (Link point1)
          ds <- f desc1 desc2
          writePoint point1 (Info (weight1 + weight2) ds)
        else do
          writePoint point1 (Link point2)
          ds <- f desc1 desc2
          writePoint point2 (Info (weight1 + weight2) ds)
      (_,_) -> error "union: bug!!!"
    
equivalent point1 point2 = do
  p1 <- repr point1
  p2 <- repr point2
  return $ p1 == p2

is_representative point = do
  l1 <- readPoint point
  case l1 of
   Link _ -> return False
   Info _ _ -> return True

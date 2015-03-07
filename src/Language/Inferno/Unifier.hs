{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# OPTIONS_GHC -fdefer-type-errors #-}

module Language.Inferno.Unifier where


import Control.Monad 
import Control.Monad.IO.Class
import Control.Applicative
import Data.Monoid

import Data.Foldable (Foldable(..))
import qualified Data.Foldable as F
import Data.Traversable (Traversable(..))
import qualified Data.Traversable as T

import Data.Typeable
import qualified Data.List as List

import Control.Monad.Catch
import Control.Monad.Ref
import Control.Monad.EqRef

import Language.Inferno.UnifierSig

import Text.PrettyPrint (Doc)
import qualified Text.PrettyPrint as PP


import Language.Inferno.TRef
import qualified Language.Inferno.VarMap as VarMap
import qualified Language.Inferno.TUnionFind as UF

import System.IO.Unsafe

---
import Control.Monad.State
import Data.IORef
import Data.Coerce
----------------------------------------------------------------

{- The data structure maintained by the unifier is as follows. -}

{-
   A unifier variable is a point of the union-find algorithm.
   We also keep an identifier with it for hashing.
-}

data Variable m s = Variable
                  { getPoint :: UF.Point m (Descriptor m s), getId :: Int }
  deriving (Typeable)

vars = unsafePerformIO (newIORef [])
add_var v = do
  vs <- readIORef vars
  writeIORef vars (v:vs)


classes = do
  vs <- readIORef vars
  c <- forM vs (\v -> do
                    d <- UF.find (getPoint v)
                    s <- readIORef (descStruc d)
                    return (getId v, descId d, s))
  let s = List.sortBy (\ (x,y,_) (z,w,_) -> compare y w)
  
  let us = List.groupBy (\ (x,y,_) (z,w,_) -> y == w) (s c)
  return us

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


--instance Eq (Variable m s) where
--  v1 == v2 = (getId v1) == (getId v2) 
  
instance Eq (Descriptor m s) where
  d1 == d2 = (descId d1) == (descId d2)

instance Show (Variable r s) where
  show v = "V" ++ (show(getId v))
  
instance Show (Descriptor r s) where
  show d = "D" ++  (show (descId d))

data Err r s = Unify (Variable r s) (Variable r s)
             | Cycle (Variable r s)
   deriving (Typeable, Show)
            
instance (Typeable s, Typeable r) => Exception (Err r s)

----------------------------------------------------------------
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

-----------------------------------------------------------------

-- creates a fresh variable with specified structure and rank
makeFresh :: (MonadRef m, MonadFresh m) =>
             Maybe (s (Variable m s)) -> Int -> m (Variable m s)
makeFresh ms rank = do
     id  <- fresh
     str <- newRef ms
     rnk <- newRef rank
     point <- UF.fresh $ Descriptor id str rnk
     let v = Variable point id
     (seq  (unsafePerformIO (add_var v))
             (return v))

-----------------------------------------------------------------

{- The internal function [unify t v1 v2] equates the variables [v1] and
   [v2] and propagates the consequences of this equation until an
   inconsistency is found or a solved form is reached. In the former
   case, [ZipError] is raised.  -}

unify_internal v1 v2 =
  {- If the two variables already belong to the same equivalence class, there
     is nothing to do, and [unify_descriptors] is not invoked. Furthermore, if
     there is something to do, then [unify_descriptors] is invoked only after
     the two equivalence classes have been merged. This is not just an
     optimization; it is essential in guaranteeing termination, since we are
     dealing with potentially cyclic structures. -}
  
  seq (unsafePerformIO (putStrLn $ show (getId v1) ++ "<=>" ++ show (getId v2)))
      UF.union unify_descriptors (getPoint v1) (getPoint v2)


-- [unify_descriptors desc1 desc2] combines the descriptors [desc1] and
-- [desc2], producing a descriptor for the merged equivalence class.
unify_descriptors desc1 desc2 = do
  s1 <- readRef (descStruc desc1)
  s2 <- readRef (descStruc desc2)
  struc <- unify_structures s1 s2
  new_struc <- newRef struc
  r1 <- readRef (descRank desc1)
  r2 <- readRef (descRank desc2)
  new_rank <- newRef (min r1 r2)
  return $ Descriptor
            (descId desc1) -- an arbitrary choice of identifier is ok
            new_struc
            new_rank

-- [unify_structures structure1 structure2] combines two structures. If one of
-- them is undefined, we just keep the other. If both are defined, we unify
-- them recursively.
unify_structures structure1 structure2 =
  case (structure1, structure2) of
    (Just s1, Just s2) -> do zipM_ unify_internal s1 s2
                             return (Just s2)  -- arbitrary, they are equal
    (Just s , Nothing) -> return (Just s)
    (Nothing, Just s ) -> return (Just s)
    (Nothing, Nothing) -> return Nothing


--------------------------------------------------------------------------
--  The public version of [unify] wraps the unification process in a
--  transaction, so that a failed unification attempt does not alter the state
--  of the unifier.
unify :: forall r m s. (Typeable m, MonadEqRef m, MonadCatch m, ZipM s,
                        Show (s (Variable m s)))
         => Variable m s -> Variable m s -> m ()
unify v1 v2 = do
  tentatively (Proxy :: Proxy (Err m s))
    (unify_internal v1 v2)
    `catch`
    (\(e :: ZipError (s (Variable m s))) ->
      throwM (Unify v1 v2))
  
    
--------------------------------------------------------------------------
equivalent
  :: (MonadEqRef m) => Variable m a -> Variable m a -> m Bool
equivalent v1 v2 = UF.equivalent (getPoint v1) (getPoint v2)

-- is_representative :: (MonadRef m) => Variable m s -> m Bool
is_representative v = UF.is_representative (getPoint v)

-------------------------------------------------------------------------

{- The occurs check, which detects cycles in the graph, cannot be
   defined as an instance of the cyclic decoder, for several reasons. For
   one thing, the cyclic decoder is inefficient, as it does not (cannot)
   mark the nodes that have been visited. Furthermore, the occurs check
   explores only the young generation, whereas the decoders explore
   everything. -}

-- new_occurs_check :: (Variable -> Bool) -> Variable -> M ()
new_occurs_check :: (MonadRef m, MonadThrow m, Typeable m, Typeable s, Foldable s) => (Variable m s -> m Bool) -> Variable m s -> m ()
new_occurs_check is_young v = do
  table <- VarMap.new 
  let -- traverse :: Variable s -> IO ()
      traverse v = do
        b <- is_young v
        when b $ do
          vi <- desc_id v
          mb <- VarMap.lookup table vi
          case mb of
            Just visited ->
              when (not visited) $
                 -- This node is in the table, but has not been fully
                 -- visited. Hence, it is being visited. A cycle has
                 -- been found.
                 throwM (Cycle v)
            Nothing -> do
              -- Mark this variable as being visited
              VarMap.insert table vi False
              -- Visit its successors.
              str <- structure v
              case str of
                 Just x  -> F.mapM_ traverse x
                 Nothing -> return ()
              VarMap.insert table vi True
  traverse v          


-----------------------------------------------------------------
-- decoding  


new_acyclic_decoder :: forall t m.
                       (MonadRef m, MonadIO m, 
                        Output t) => m (Variable m (Src t) -> m t)
new_acyclic_decoder = do
  table <- VarMap.new
  
  let decode :: Variable m (Src t) -> m t
      decode v = do
        vi <- desc_id v
        mv <- VarMap.lookup table vi
        case mv of
         Just a  -> do
           return a
         Nothing -> do
           ms <- structure v
           a <- case ms of
                    Nothing -> do
                      i <- desc_id v
                      let a = tovar i
                      return $ a
                    Just t  -> liftM struc (T.mapM decode t)
           VarMap.insert table vi a
           return a
          
  return $ decode

-----------------------------------------------------------------
-- Some testing code. 

{-
data Struct a =
    Base Int
  | One a
  | Two a a
    deriving (Eq,Show,Foldable,Traversable,Functor,Typeable)

instance ZipM Struct where
  zipM f (Base i) (Base j) | i == j = return (Base i)
  zipM f (One x) (One y) = do z <- f x y
                              return $ One z
  zipM f (Two x1 x2) (Two y1 y2) = do
    z1 <- f x1 y1
    z2 <- f x2 y2
    return (Two z1 z2)
  zipM f x y = throwM (ZipError x y)

  zipM_ f (Base i) (Base j) = return ()
  zipM_ f (One x) (One y) = f x y
  zipM_ f (Two x1 x2) (Two y1 y2) = f x1 y1 >> f x2 y2
  zipM_ f x y = throwM (ZipError x y)

newtype Mu f = Roll (f (Mu f))
instance Show (Mu Struct) where
  show (Roll s) = case (fmap show s) of
    Base i -> "B" ++ show i
    One  x -> "One " ++ x
    Two x y -> "Two " ++ x ++ " " ++ y
  

type Ty = Mu Struct

instance Output Ty where
  type Src Ty = Struct
  tovar x = Roll (Base x)
  struc   = Roll 


newtype M a = M (StateT Int IO a)
  deriving (Typeable, Functor, Applicative, Monad)

instance MonadEqRef M where
  type Ref M = IORef
  newRef  = coerce (newRef :: a -> StateT Int IO a)
  readRef = coerce readRef
  writeRef = coerce writeRef
  eqRef = coerce eqRef

instance MonadFresh M where
  fresh = do
    x <- get
    put (x + 1)
    return x

test :: M ()
test = do
  x <- makeFresh Nothing 0
  w <- makeFresh Nothing 0
  m <- makeFresh (Just (Base 42)) 0
  y <- makeFresh (Just (Two m w)) 0
  z <- makeFresh (Just (Two x x)) 0
  unify y z
  b <- equivalent w m

  (decode :: Variable M Struct -> M Ty) <- new_acyclic_decoder 
  o1 <- decode x
  o2 <- decode w
  o3 <- decode m
  o4 <- decode y
  o5 <- decode z
  liftIO $ print [o1, o2, o3,o4, o5]
  return ()

go :: IO ()
go = evalStateT test 0
  
 
-}

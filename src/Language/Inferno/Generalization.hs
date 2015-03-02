{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes, ScopedTypeVariables #-}
{-# OPTIONS_GHC -fdefer-type-errors #-}

module Language.Inferno.Generalization
       (Scheme, quantifiers, body,
        State, initialize, no_rank, register, trivial,
        enter, exit, instantiate)
       where

import Language.Inferno.UnifierSig
import qualified Language.Inferno.Unifier as U

import Data.Array.MArray
import Language.Inferno.InfiniteArray (InfiniteArray)
import qualified Language.Inferno.InfiniteArray as InfiniteArray

-- import Data.IORef
import Control.Monad
import Control.Monad.Ref
import Data.Typeable
import Control.Monad.Catch

import qualified Data.Traversable as T
import qualified Data.Foldable as F

import qualified Data.Maybe as Maybe

import qualified Language.Inferno.TRefMap as TRefMap

{- The [Generalization] module manages the [rank] fields of the
unification variables, as well as a global notion of ``current rank'',
stored in the field [state.young]. Ranks can be thought of as de
Bruijn levels, in the following sense: whenever the left-hand side of
a [CLet] constraint is entered, the current rank is incremented by
one. Thus, the rank of a variable indicates where (i.e., at which
[CLet] construct) this variable is (existentially) bound. -}

{- The rank of a variable is set to the current rank when the variable is
   first created. During the lifetime of a variable, its rank can only
   decrease. Decreasing a variable's rank amounts to hoisting out the
   existential quantifier that binds this variable. -}

{- Ranks are updated in a lazy manner. Only one rank maintenance
operation takes place during unification: when two variables are
unified, the rank of the merged variable is set to the minimum of the
ranks of the two variables. (This operation is performed by the
unifier.) Two other rank maintenance operations are performed here,
namely downward propagation and upward propagation. Downward
propagation updates a child's rank, based on its father rank; there is
no need for a child's rank to exceed its father's rank. Upward
propagation updates a father's rank, based the ranks of all of its
children: there is no need for a father's rank to exceed the maximum
of its children's ranks. These operations are performed at
generalization time because it would be costly (and it is unnecessary)
to perform them during unification. -}

{- The [rank] field maps every variable to the [CLet] construct where it
is bound. Conversely, the [Generalization] module keeps track, for
every active [CLet] construct, of a (complete) list of variables that
are bound there. This takes the form of an array, stored in the field
[state.pool].  For every rank comprised between 1 and [state.young],
both included, this array stores a list of the variables that are
bound there. This array is again updated in a lazy manner, at
generalization time. Because the unifier updates the ranks, but does
not know about this array, the property that holds in general is: if a
variable [v] has rank [i], then it appears in pool number [j], where
[i <= j] holds. Immediately after generalization has been performed,
the array has been updated, so [i = j] holds. -}

data State m ra s = State {
  pool  :: InfiniteArray m ra [U.Variable m s],
  young :: (Ref m) Int
}

data Scheme m s = Scheme {
  quantifiers :: [U.Variable m s],
  body        :: U.Variable m s
}

-- type Fresher s = (Maybe (s (U.Variable s)) -> Int -> IO (U.Variable s))

generic, no_rank, base_rank :: Int
generic = -1
no_rank = 0
base_rank = no_rank + 1

-- needs a fresheness function passed to it
initialize :: forall m ra s.
              (MonadRef m, MArray ra [U.Variable m s] m) =>  m (State m ra s)
initialize = do
  a <- InfiniteArray.make 8 ([] :: [U.Variable m s])
  r <- newRef no_rank
  return $ State a r 

{- Trivial constructor of type Schemes -}
trivial = Scheme []

register_at_rank state v = do
  rank <- U.rank v
  vs <- InfiniteArray.get (pool state) rank
  InfiniteArray.set (pool state) rank (v : vs)

{- The external function [register] assumes that [v]'s rank is
uninitialized.  It sets this rank to the current rank, [state.young],
then registers [v]. -}
register state v = do
  y <- readRef (young state)
  U.set_rank v y
  register_at_rank state v

enter state = do
  y <- readRef (young state)
  writeRef (young state) (y+1)

-- again, we should be able to do better than a list
-- for cycle detection
make_scheme :: forall m s. (F.Foldable s, MonadRef m) =>
   (U.Variable m s -> m Bool) -> U.Variable m s -> m (Scheme m s)
make_scheme is_generic body = do
  table <- TRefMap.new U.equivalent
  let traverse :: (U.Variable m s) -> [U.Variable m s] -> m [U.Variable m s]
      traverse v quantifiers = do
        visited <- TRefMap.member table v
        b <- is_generic v
        if (not b ||  visited) then
          return quantifiers
          else do
            TRefMap.insert table v ()
            ms <- U.structure v
            case ms of
              Nothing ->
                return $ v : quantifiers
              Just t ->
                F.foldrM traverse quantifiers t
              
  quantifiers <- traverse body []
  return (Scheme quantifiers body)

----------------------------------------------------------------
-- exit is where the moderately subtle generalizatio work takes place

exit :: forall m s ra. (MonadRef m, MonadThrow m,
         F.Foldable s, Typeable m, Typeable s,
         MArray ra [U.Variable m s] m)
        => Bool -> State m ra s -> [U.Variable m s]
        -> m ([U.Variable m s], [Scheme m s])
exit rectypes state roots = do
  -- all the variables in the young generation
  y <- readRef (young state)
  vs <- InfiniteArray.get (pool state) y

  -- This hash table stores all of these variables, so that we may check
  -- membership in the young generation in constant time.
  young_generation <- TRefMap.new U.equivalent

  -- This array stores all of these variables, indexed by rank.
  sorted <- (newArray (0, y + 1) [] :: m (ra Int [U.Variable m s]))

  -- initialize data structures
  forM vs (\v -> do
              TRefMap.insert young_generation v ()
              rank <- U.rank v
              vs <- readArray sorted rank
              writeArray sorted rank (v : vs))
    
  -- membership test for young generation
  let is_young v =
        TRefMap.member young_generation v

  -- If the client would like us to detect and rule out recursive types, then
  -- now is the time to perform an occurs check over the young generation.
  when (not rectypes) $
    forM_ vs (U.new_occurs_check is_young)

  -- Now, update the rank of every variable in the young generation.
  visited <- TRefMap.new U.equivalent

  forM [base_rank .. y] (\ k -> do
     let traverse v = do
           b <- TRefMap.member visited v
           if b then return ()
              else do
             TRefMap.insert visited v ()
             U.adjust_rank v k
             b <- is_young v
             if not b then return ()
               else do
               o <- (U.structure v)
               case o of
                Nothing -> return ()
                Just t  -> do
                  F.foldr (\ child accu -> do
                     traverse child
                     r <- U.rank child
                     a <- accu
                     return (max r a)) (return base_rank) t
                  return ()
     
                
     vs <- readArray sorted k
     forM vs traverse)
  -- Every variable whose rank is still [young] must be generalized.
  vs' <- filterM (\ v -> do
          b <- U.is_representative v
          if not b then return False else do
            r <- U.rank v
            if r < y then do
                _ <- register_at_rank state v
                return False
              else do
                U.set_rank v generic
                str <- U.structure v
                return (Maybe.isNothing str)) vs
         
  -- Update the state by emptying the current pool and decreasing [young].
  InfiniteArray.set (pool state) y []
  writeRef (young state) (y - 1)

  -- This auxiliary function recognizes the variables that we have just
  -- marked as generic.

  let is_generic v = do
        r <- U.rank v
        return $ r == generic
        
  schemes <- forM roots (make_scheme is_generic)
  
  return (vs', schemes)


----------------------------------------------------------------
instantiate :: forall m ra s.
               (T.Traversable s,
                MonadRef m,
                MonadFresh m,
                MArray ra [U.Variable m s] m) =>
               State m ra s -> Scheme m s -> m ([U.Variable m s], U.Variable m s)
instantiate state scheme = do
  visited <- TRefMap.new U.equivalent
  let copy :: U.Variable m s -> m (U.Variable m s)
      copy v = do
        rnk <- U.rank v
        if rnk > 0 then return v
          else do
            unless (rnk == generic) $ error "instantiate assertion"
            vs <- TRefMap.lookup visited v
            case vs of
              Just x  -> return x
              Nothing -> do
                y  <- readRef (young state)
                v' <- U.makeFresh Nothing y
                register_at_rank state v'
                TRefMap.insert visited v v'
                ms <- U.structure v
                case ms of
                   Nothing -> U.set_structure v' Nothing
                   Just s  -> do
                     s' <- T.mapM copy s
                     U.set_structure v' (Just s')
                return v'
  liftM2 (,) (mapM copy (quantifiers scheme)) (copy (body scheme))

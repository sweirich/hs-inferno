{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes, ScopedTypeVariables #-}
{-# OPTIONS_GHC -fdefer-type-errors #-}

module Language.Inferno.Generalization
--       (Scheme, quantifiers, body,
--        State, initialize, no_rank, register, trivial,
--        enter, exit, instantiate)
       where

import Language.Inferno.UnifierSig
import qualified Language.Inferno.Unifier as U

import Data.Array.MArray
import Language.Inferno.InfiniteArray (InfiniteArray)
import qualified Language.Inferno.InfiniteArray as InfiniteArray

-- import Data.IORef
import Control.Monad
import Control.Monad.Ref
import Control.Monad.IO.Class

import Data.Typeable
import Control.Monad.Catch

import qualified Data.Traversable as T
import qualified Data.Foldable as F

import qualified Data.Maybe as Maybe

import qualified Language.Inferno.VarMap as VarMap

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
  -- an array of pools (lists of variables), indexed by ranks
  pool  :: InfiniteArray m ra [U.Variable m s],
  -- the current rank
  young :: (Ref m) Int
}

{-
   The generic variables that have no structure are the ``quantifiers'' of the
   type scheme. A type scheme is internally represented as a pair of a list of
   quantifiers and a root variable, the ``body''. The order of the quantifiers
   is arbitrarily chosen, but once fixed, matters; the functions [quantifiers]
   and [instantiation] must agree on this order. The quantifiers are exactly
   the variables that are reachable from the body, have rank [generic], and
   have no structure.
-}

data Scheme m s = Scheme {
  quantifiers :: [U.Variable m s],
  body        :: U.Variable m s
}


--------------------------------------------------------------------------

generic, no_rank, base_rank :: Int

-- The constant [generic] is defined as [-1]. This rank is used for the variables
-- that form the generic (to-be-copied) part of a type scheme. 
generic = -1
-- The rank [no_rank] is defined as [0]. This rank is used when a variable is
-- freshly created and is not known to us yet.
no_rank = 0
-- The positive ranks are valid indices into the pool array.
base_rank = no_rank + 1

-------------------------------------------------------------------------

-- The pool array is initially populated with empty pools. The current rank is
-- initially set to 0, so the first rank that is actually exploited is 1.
initialize :: forall m ra s.
              (MonadRef m, MArray ra [U.Variable m s] m) =>  m (State m ra s)
initialize = do
  a <- InfiniteArray.make 8 ([] :: [U.Variable m s])
  r <- newRef no_rank
  return $ State a r 

--------------------------------------------------------------------------
{- Trivial constructor of type Schemes -}
trivial = Scheme []

 -------------------------------------------------------------------------- *)

-- The internal function [register_at_rank] assumes that [v]'s rank is already
-- a valid positive rank, and registers [v] by inserting it into the
-- appropriate pool.

register_at_rank state v = do
  rank <- U.rank v
  y <- readRef (young state)
  unless (0 < rank && rank <= y) $ error "BUG: register_at_rank"
  vs   <- InfiniteArray.get (pool state) rank
  InfiniteArray.set (pool state) rank (v : vs)

-- The external function [register] assumes that [v]'s rank is
-- uninitialized.  It sets this rank to the current rank, [state.young],
-- then registers [v]. 
register state v = do
  rank <- U.rank v
  unless (rank == no_rank) $ error "BUG: register"
  y <- readRef (young state)
  U.set_rank v y
  register_at_rank state v

--------------------------------------------------------------------------

-- [enter] simply increments the current rank by one. The corresponding pool is
-- in principle already empty.  
enter state = do
  y <- readRef (young state)
  writeRef (young state) (y+1)
  vs <- InfiniteArray.get (pool state) (y+1)
  unless (null vs) $ error "BUG: enter not empty"

--------------------------------------------------------------------------
{- The internal function [make_scheme] turns a variable, [body], into a type
   scheme. The body of the type scheme is [body]. The quantifiers of the type
   scheme are exactly the generic structureless variables that are reachable,
   in the unification graph, from [body]. The function [is_generic] determines
   which variables are generic. -}
  
-- again, we should be able to do better than a list
-- for cycle detection
make_scheme :: forall m s. (F.Foldable s, MonadRef m) =>
   (U.Variable m s -> m Bool) -> U.Variable m s -> m (Scheme m s)
make_scheme is_generic body = do
  table <- VarMap.new 
  let traverse :: (U.Variable m s) -> [U.Variable m s] -> m [U.Variable m s]
      traverse v quantifiers = do
        vi <- U.desc_id v
        visited <- VarMap.member table vi
        b <- is_generic v
        if (not b ||  visited) then
          return quantifiers
          else do
            VarMap.insert table vi ()
            ms <- U.structure v
            case ms of
              Nothing ->
                return $ v : quantifiers
              Just t ->
                F.foldrM traverse quantifiers t
              
  quantifiers <- traverse body []
  return (Scheme quantifiers body)

----------------------------------------------------------------
-- exit is where the moderately subtle generalization work takes place

exit :: forall m s ra. (MonadRef m, MonadThrow m, MonadIO m,
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
  young_generation <- VarMap.new

  -- This array stores all of these variables, indexed by rank.
  sorted <- (newArray (0, y + 1) [] :: m (ra Int [U.Variable m s]))

  -- initialize data structures
  forM vs (\v -> do
              vi <- U.desc_id v
              VarMap.insert young_generation vi ()
              rank <- U.rank v
              vs <- readArray sorted rank
              writeArray sorted rank (v : vs))
    
  -- membership test for young generation
  let is_young v = do
        vi <- U.desc_id v
        VarMap.member young_generation vi

  -- If the client would like us to detect and rule out recursive types, then
  -- now is the time to perform an occurs check over the young generation.
  when (not rectypes) $
    forM_ vs (U.new_occurs_check is_young)

  -- Now, update the rank of every variable in the young generation.
  visited <- VarMap.new

  y <- readRef (young state)
  forM [base_rank .. y] (\ k -> do

     -- A postcondition of [traverse v] is [U.rank v <= k]. (This is downward
     -- propagation.)
     let traverse v = do
           rnk <- U.rank v
           unless (rnk > 0) $ error "BUG in exit"

           -- If [v] was visited before, then its rank must be below [k], as we
           -- adjust ranks on the way down already. 
           vi <- U.desc_id v
           b <- VarMap.member visited vi
           if b then unless (rnk <= k) $ error "Another bug in exit"
              else do
             -- Otherwise, immediately mark it as visited, and immediately adjust
             -- its rank so as to be at most [k]. (This is important if cyclic
             -- graphs are allowed.)
             VarMap.insert visited vi ()
             U.adjust_rank v k
             -- If [v] is part of the young generation, and if it has structure,
             -- then traverse its children (updating their ranks) and on the way
             -- back up, adjust [v]'s rank again (this is upward propagation). If
             -- [v] has structure but no children, then it is a constant, and it
             -- receives the base rank; it will be moved to the oldest pool. If
             -- [v] has no structure, do nothing; it would be wrong to move its
             -- rank down to the base rank.
             b <- is_young v
             if b then do
               -- The rank of this variable can't have been below [k], because
               -- it is young but was not visited yet. Thus, it must have been
               -- at or above [k], and since we have just adjusted it, it must
               -- now be [k].
               nrnk <- U.rank v
               unless (nrnk == k) $ error "Can't be below k"
               o <- (U.structure v)
               case o of
                Nothing -> return ()
                Just t  -> do
                  r <- F.foldr (\ child accu -> do
                                   traverse child
                                   r <- U.rank child
                                   a <- accu
                                   return (max r a)) (return base_rank) t
                  U.adjust_rank v r
               else do
                  nrnk <- U.rank v
                  y <- readRef (young state)
                  when (nrnk < y) $ error "BUG here"
     
                
     vs <- readArray sorted k
     forM vs traverse)
  -- Every variable whose rank is still [young] must be generalized.
  vs' <- filterM (\ v -> do
          b <- U.is_representative v
          if not b then return False else do
            y <- readRef (young state)
            r <- U.rank v
            if r < y then do
                register_at_rank state v
                return False
              else do
                unless (r == y) $ error "bug bug bug"
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

  forM_ vs' (\v -> do 
                vi <- U.desc_id v
                liftIO $ putStrLn $ "Generalizing " ++ show vi)
  
  return (vs', schemes)


----------------------------------------------------------------
--  Instantiation amounts to copying a fragment of a graph. The fragment that
--  must be copied is determined by inspecting the rank -- [generic] means
--  copy, a positive rank means don't copy.
instantiate :: forall m ra s.
               (T.Traversable s,
                MonadRef m,
                MonadFresh m, MonadIO m,
                MArray ra [U.Variable m s] m) =>
               State m ra s -> Scheme m s -> m ([U.Variable m s], U.Variable m s)
instantiate state scheme = do
  qsi <- mapM U.desc_id (quantifiers scheme)
  mapM (\i -> do
              liftIO $ putStrLn $ "freshening: " ++ show i) qsi
  --  Prepare to mark which variables have been visited and record their copy. 
  visited <- VarMap.new 
  -- If the variable [v] has rank [generic], then [copy v] returns a copy of
  -- it, and copies its descendants recursively. If [v] has positive rank,
  -- then [copy v] returns [v]. Only one copy per variable is created, even if
  -- a variable is encountered several times during the traversal. 

  let copy :: U.Variable m s -> m (U.Variable m s)
      copy v = do

        -- If this variable has positive rank, then it is not generic: we must
        -- stop.
        vi <- U.desc_id v
        rnk <- U.rank v
        if rnk > 0 then do
          liftIO $ putStrLn $ "copy: rank>0 for " ++ (show vi)
          return v

          else do
            unless (rnk == generic) $ error "instantiate assertion"

            -- If a copy of this variable has been created already, return it.
            vi <- U.desc_id v
            vs <- VarMap.lookup visited vi
            case vs of
              Just x  -> do
                xi <- U.desc_id x
                liftIO $ putStrLn $ "copy: found " ++ (show vi) ++ " as " ++ (show xi)
                return x
              Nothing -> do
                -- The variable must be copied, and has not been copied yet. Create a
                -- new variable, register it, and update the mapping. Then, copy its
                -- descendants. Note that the mapping must be updated before making a
                -- recursive call to [copy], so as to guarantee termination in the
                -- presence of cyclic terms.
                y  <- readRef (young state)
                v' <- U.makeFresh Nothing y
                vi' <- U.desc_id v'
                liftIO $ putStrLn $ "copy: mapping "
                  ++ (show vi) ++ " to " ++ (show vi')
                register_at_rank state v'
                VarMap.insert visited vi v'
                ms <- U.structure v
                case ms of
                   Nothing -> U.set_structure v' Nothing
                   Just s  -> do
                     s' <- T.mapM copy s
                     U.set_structure v' (Just s')
                return v'

  
  liftM2 (,) (mapM copy (quantifiers scheme)) (copy (body scheme))

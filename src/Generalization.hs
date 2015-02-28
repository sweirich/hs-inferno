{-# LANGUAGE RankNTypes, ScopedTypeVariables #-}
{-# OPTIONS_GHC -fdefer-type-errors #-}

module Generalization
       (Scheme, quantifiers, body,
        Fresher, 
        State, initialize, no_rank, register, trivial,
        enter, exit, instantiate)
       where

import qualified Unifier as U
import InfiniteArray (InfiniteArray)
import qualified InfiniteArray

import Data.IORef
import Control.Monad

import qualified Data.Traversable as T
import qualified Data.Foldable as F

import qualified TRefMap

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

data State s = State {
  pool  :: InfiniteArray [U.Variable s],
  young :: IORef Int,
  fresh :: Maybe (s (U.Variable s)) -> Int -> IO (U.Variable s)
}

data Scheme s = Scheme {
  quantifiers :: [U.Variable s],
  body        :: U.Variable s
}

type Fresher s = (Maybe (s (U.Variable s)) -> Int -> IO (U.Variable s))

generic, no_rank :: Int
generic = -1
no_rank = 0
base_rank = no_rank + 1

-- needs a fresheness function passed to it
initialize :: IO (State s)
initialize fr = do
  a <- InfiniteArray.make 8 []
  r <- newIORef no_rank
  return $ State a r fr

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
  y <- readIORef (young state)
  U.set_rank v y
  register_at_rank state v

enter state = do
  y <- readIORef (young state)
  writeIORef (young state) (y+1)

-- again, we should be able to do better than a list
-- for cycle detection
make_scheme :: forall s. (F.Foldable s) =>
   (U.Variable s -> Bool) -> U.Variable s -> IO (Scheme s)
make_scheme is_generic body = do
  table <- TRefMap.new
  let traverse :: (U.Variable s) -> [U.Variable s] -> IO [U.Variable s]
      traverse v quantifiers = do
        visited <- TRefMap.member table v
        if (not (is_generic v) ||  visited) then
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
  
exit rectypes state roots = undefined

instantiate :: forall s. (T.Traversable s) => State s -> Scheme s -> IO ([U.Variable s], U.Variable s)
instantiate state scheme = do
  visited <- TRefMap.new 
  let copy :: U.Variable s -> IO (U.Variable s)
      copy v = do
        rnk <- U.rank v
        if rnk > 0 then return v
          else do
            vs <- TRefMap.lookup visited v
            case vs of
              Just x  -> return x
              Nothing -> do
                y <- readIORef (young state)
                v' <- (fresh state) Nothing y
                register_at_rank state v'
                TRefMap.insert visited v v'
                ms <- U.structure v
                case ms of
                   Nothing -> U.set_structure v' Nothing
                   Just s  -> do
                     --- (a -> m a) -> s a -> m (s a)
                     s' <- T.mapM copy s
                     U.set_structure v' (Just s')
                return v'
  liftM2 (,) (mapM copy (quantifiers scheme)) (copy (body scheme))

{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -fdefer-type-errors #-}
module Language.Inferno.M.SolverHi where

import Control.Monad
import Control.Applicative

import Control.Monad.IO.Class
import Control.Monad.Catch
import Control.Monad.Ref

import Data.Typeable

-- The Structure and Output classes
import Data.Traversable (Traversable)
import Language.Inferno.UnifierSig

-- We rely on the low-level solver interface
import Language.Inferno.SolverM (M)
import qualified Language.Inferno.M.SolverLo as Lo
import qualified Language.Inferno.M.Unifier as U

type TermVar = Lo.TermVar
type Var s   = Lo.Var s

{- We now set up the applicative functor API, or combinator API, to the
   solver. The constraint construction phase and the witness decoding phase
   are packaged together, with two benefits: 1- the syntax of constraints and
   witnesses, as well as the details of write-once references, are hidden; 2-
   the client can write code in a compositional and declarative style, under
   the illusion that constructing a query immediately gives rise to an
   answer. 

   The client is allowed to construct objects of type ['a co]. Such an object is
   a pair of a constraint and a continuation. It is evaluated in two phases. In
   the first phase, the constraint is solved. In the second phase, the continuation
   is invoked. It is allowed to examine the witness, and must produce a value of
   type ['a]. 

   The continuation has access to an environment of type [env]. For the moment,
   the environment is just a type decoder.  -}

type Env t = Lo.Decoder t

data Co t a = Co (Lo.RawCo (Src t)) (Env t -> M a)

instance Show (Co t a) where
  show (Co rc k) = show rc

--------------------------------------------------------------------------

-- the type forms an applicative functor

instance Functor (Co t) where
  fmap f (Co rc k) = Co rc  (\env -> liftM f (k env))

-- the pairing operation (from McBride & Patterson's Monoidal class)
  
(Co rc1  k1) ^& (Co rc2 k2) =
  Co (Lo.CConj rc1 rc2) (\env -> liftM2 (,) (k1 env) (k2 env))

-- a variant of the above which builds a conjunction constraint
-- but drops the first component of the pair and keeps only the second.

(Co rc1  k1) ^^ (Co rc2 k2) =
  Co (Lo.CConj rc1 rc2) (\env -> (k1 env) >> (k2 env))

instance Applicative (Co t) where
  pure x = (Co Lo.CTrue (\ env -> return x))
  mf <*> mx = fmap (\(f,x) -> f x) (mf ^& mx)

-- the Co type does not form a monad. There is no bind.
-- but this operation is useful for structuring coercions.

(<$$>) :: M (Co s a) -> (a -> b) -> M (Co s b)
cm <$$> f = liftM (fmap f) cm


--------------------------------------------------------------------------

-- existential quantification

-- exist_aux ::  Maybe (Src t (Var (Src t)))
--             -> (Var (Src t) -> M (Co t a)) -> M (Co t (t, a))
exist_aux t f = do
  v <- Lo.makeFresh t
  Co rc k <- f v
  let raw_co = (Lo.CExist v rc)
  return $ Co raw_co
              (\ decode -> do t <- decode v
                              a <- k decode
                              return (t, a))

exist :: forall t a. (Traversable (Src t)) =>
         (Var (Src t) -> M (Co t a)) -> M (Co t (t,a))
exist f = exist_aux (Nothing :: Maybe (Src t (Var (Src t)))) f

construct t f = exist_aux (Just t) f

exist_aux_ :: Maybe (Src t (U.Variable (Src t)))
              -> (U.Variable (Src t) -> M (Co t a)) -> M (Co t a)
exist_aux_ t f = do
  v <- Lo.makeFresh t
  Co rc k <- f v
  return $ Co (Lo.CExist v rc) k

exist_ f = exist_aux_ Nothing f
   -- This is logically equivalent to [exist f >>= snd], but saves a
   -- call to [decode] as well as some memory allocation.

construct_ t f = exist_aux_ (Just t) f 

{-                 
liftS :: (a ->        Var (Src t)  -> M (Co t b)) 
      -> a -> Src t (Var (Src t)) -> M (Co t b)
-}
liftS f v1 t2 = construct_ t2 $ \v2 -> f v1 v2

--------------------------------------------------------------------------
-- Equations

-- an equality constraint on the type variables v1 and v2
-- (-=-) :: Var (Src t) -> Var (Src t) -> Co t ()
v1 -=- v2 = Co (Lo.CEq v1 v2) (\env -> return ())

-- equate a variable with a shallow type.
(-==-) :: Var (Src t) -> Src t (Var (Src t)) -> M (Co t ())
(-==-) = liftS (\ v1 v2 -> return (v1 -=- v2))


-------------------------------------------------------------------------

-- Instantiation constraints

inst :: TermVar -> Var (Src t) -> M (Co t [t])
inst x v = do
  witnesses <- newRef []
  return $ Co (Lo.CInstance x v witnesses)
              (\ decode -> do
                    ws <- readRef witnesses
                    mapM decode ws)

--------------------------------------------------------------------------

-- Constraint abstractions -

-- The [CDef] form is so trivial that it deserves its own syntax. Viewing it
-- as a special case of [CLet] would be more costly (by a constant factor). 

-- def :: TermVar -> Var (Src t) -> Co t a -> Co t a
def x v (Co rc k) = Co (Lo.CDef x v rc) k

-- The general form of [CLet] involves two constraints, the left-hand side and
-- the right-hand side, yet it defines a *family* of constraint abstractions,
-- bound to the term variables [xs].

data Letn t a b  =
  Letn
  { genvars :: [Int],        -- vars to generalize
    rhs     :: a,            -- 
    rhs_ty  :: [([Int],t)],  -- type schemes for the xs
    body    :: b }
  


letn :: (Output t) =>
        [TermVar]
        -> ([Var (Src t)] -> M (Co t a))
        -> Co t b
        -> M (Co t (Letn t a b))

letn xs f1 (Co rc2 k2) = do
  -- For each term variable [x], create a fresh type variable [v], as in
  -- [CExist]. Also, create an uninitialized scheme hook, which will receive
  -- the type scheme of [x] after the solver runs. 
  xvss <- mapM (\x -> do
                   v <- Lo.makeFresh Nothing
                   sh <- newRef Nothing
                   return (x, v, sh)) xs
  -- Pass the vector of type variables to the user-supplied function [f1],
  -- as in [CExist].          
  let vs = map (\(_,v,_) -> v) xvss
  (Co rc1 k1) <- f1 vs

  -- Create one more hook, which will receive the list of
  -- all generalizable variables in the left-hand side.
  generalizable_hook <- newRef Nothing

  let raw_co = (Lo.CLet generalizable_hook rc1 xvss rc2) 
  
  -- Build a CLet constraint
  return $ Co raw_co
    (\ env -> do
        -- In the decoding phase, read the write-once references
        Just g <- readRef generalizable_hook
        generalizable <- mapM Lo.decode_variable g
        ss <- mapM (\ (_,_,scheme_hook) -> do
                       Just sh <- readRef scheme_hook
                       Lo.decode_scheme env sh) xvss
        -- and return their values to the user, in addition to the values
        -- produced by the continuations [k1] and [k2]
        a <- k1 env
        b <- k2 env
        return (Letn generalizable a ss b))
{-
let1 :: (Output t) => TermVar
        -> (Var (Src t) -> M (Co t a))
        -> Co t b
        -> M (Co t ([Int], a, ([Int],t), b))
-}
let1 x f1 c2 = do
  c <- letn [ x ] (\ [x] -> f1 x) c2
  return $ fmap
    (\(Letn generalizable v1 [ss] v2) ->
               (generalizable, v1, ss, v2)) c
  
{-  
let0 :: (Output t) =>
        Co t a ->
        M (Co t ([Int], a))
-}
let0 c1 = do
  letn [] (\ _ -> return c1) (pure ())
    <$$>
    (\ (Letn generalizable v1 _ ()) ->
          (generalizable, v1))

--------------------------------------------------------------------
-- running a constraint

{- The constraint [c] should have been constructed by [let0], otherwise we
   risk encountering variables that we cannot register. Recall that
   [G.register] must not be called unless [G.enter] has been invoked first. Of
   course, we could accept any old constraint from the user and silently wrap
   it in [let0], but then, what would we do with the toplevel quantifiers? -}

data Err t =
    Unify t t
  | Cycle t
    deriving (Typeable, Show)

instance (Show t, Typeable t) => Exception (Err t)
             
solve :: forall t a.
         (ZipM (Src t), Show ((Src t) (Var (Src t))), 
          Output t) =>
         Bool -> Co t a  -> M a
solve rectypes (Co rc k) = do
  Lo.solve rectypes rc
    `catch` (\ (e :: U.Err (Src t)) ->
              case e of
                (U.Unify v1 v2) -> do
                  decode <- (Lo.new_decoder :: M (Lo.Decoder t))
                  t1 <- decode v1
                  t2 <- decode v2
                  (throwM (Unify t1 t2))
                (U.Cycle v)     -> do
                  decode <- (Lo.new_decoder :: M (Lo.Decoder t))
                  t <- decode v
                  (throwM (Cycle t)))
  decode <- Lo.new_decoder 
  k decode
  
        
    

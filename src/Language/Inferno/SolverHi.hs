{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -fdefer-type-errors #-}
module Language.Inferno.SolverHi where

-- import Data.IORef
import Control.Monad
import Control.Applicative

import Control.Monad.Ref
import Control.Monad.EqRef
import Control.Monad.Catch
import Control.Monad.IO.Class

import Data.Typeable
import Data.Array.MArray


-- The Structure and Output classes
import Data.Traversable (Traversable)
import Language.Inferno.UnifierSig

-- We rely on the low-level solver interface
import qualified Language.Inferno.SolverLo as Lo
import qualified Language.Inferno.Unifier as U
type TermVar = Lo.TermVar
type Var m s = Lo.Var m s

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

type Env m t = Lo.Decoder m t

data Co m t a = Co (Lo.RawCo m (Src t)) (Env m t -> m a)

instance Show (Co m t a) where
  show (Co rc k) = show rc

--------------------------------------------------------------------------

-- the type forms an applicative functor

instance (Monad m) => Functor (Co m t) where
  fmap f (Co rc k) = Co rc  (\env -> liftM f (k env))

-- the pairing operation (from McBride & Patterson's Monoidal class)
  
(Co rc1  k1) ^& (Co rc2 k2) =
  Co (Lo.CConj rc1 rc2) (\env -> liftM2 (,) (k1 env) (k2 env))

-- a variant of the above which builds a conjunction constraint
-- but drops the first component of the pair and keeps only the second.

(Co rc1  k1) ^^ (Co rc2 k2) =
  Co (Lo.CConj rc1 rc2) (\env -> (k1 env) >> (k2 env))

instance (Monad m) => Applicative (Co m t) where
  pure x = (Co Lo.CTrue (\ env -> return x))
  mf <*> mx = fmap (\(f,x) -> f x) (mf ^& mx)

-- the Co type does not form a monoid. There is no bind.
-- but this operation is useful for structuring coercions.

(<>) :: Monad m => m (Co m s a) -> (a -> b) -> m (Co m s b)
cm <> f = liftM (fmap f) cm


--------------------------------------------------------------------------

-- existential quantification

-- exist_aux :: (MonadFresh m, MonadRef m, MonadIO m) => Maybe (Src t (Var m (Src t))) -> (Var m (Src t) -> m (Co m t a)) -> m (Co m t (t, a))
exist_aux t f = do
  v <- Lo.makeFresh t
  Co rc k <- f v
  let raw_co = (Lo.CExist v rc)
  liftIO $ putStrLn $ "new constraint:" ++ (show raw_co)
  return $ Co raw_co
              (\ decode -> do t <- decode v
                              a <- k decode
                              return (t, a))

exist :: forall m t a. (MonadFresh m, MonadRef m, MonadIO m, Traversable (Src t)) =>
         (Var m (Src t) -> m (Co m t a)) -> m (Co m t (t,a))
exist f = exist_aux (Nothing :: Maybe (Src t (Var m (Src t)))) f

construct t f = exist_aux (Just t) f

exist_aux_ :: (MonadIO m, MonadFresh m, MonadRef m) 
              => Maybe (Src t (U.Variable m (Src t)))
              -> (U.Variable m (Src t) -> m (Co m t a)) -> m (Co m t a)
exist_aux_ t f = do
  v <- Lo.makeFresh t
  Co rc k <- f v
  liftIO $ putStrLn $ "new constraint: exists " ++ show (U.getId v)
  return $ Co (Lo.CExist v rc) k

exist_ f = exist_aux_ Nothing f
   -- This is logically equivalent to [exist f >>= snd], but saves a
   -- call to [decode] as well as some memory allocation.

construct_ t f = exist_aux_ (Just t) f 

{-                 
liftS :: (MonadFresh m, MonadRef m) =>
     (a ->        Var m (Src t)  -> m (Co m t b)) 
   -> a -> Src t (Var m (Src t)) -> m (Co m t b)
-}
liftS f v1 t2 = construct_ t2 $ \v2 -> f v1 v2

--------------------------------------------------------------------------
-- Equations

-- an equality constraint on the type variables v1 and v2
-- (-=-) :: Monad m => Var m (Src t) -> Var m (Src t) -> Co m t ()
v1 -=- v2 = Co (Lo.CEq v1 v2) (\env -> return ())

-- equate a variable with a shallow type.
(-==-) :: (MonadFresh m, MonadRef m, MonadIO m) =>
     Var m (Src t) -> Src t (Var m (Src t)) -> m (Co m t ())
(-==-) = liftS (\ v1 v2 -> return (v1 -=- v2))


-------------------------------------------------------------------------

-- Instantiation constraints

inst :: (MonadRef m, MonadIO m) => TermVar -> Var m (Src t) -> m (Co m t [t])
inst x v = do
  liftIO $ putStrLn $ "new constraint: inst " ++ show x ++ " to " ++ show (U.getId v)
  witnesses <- newRef []
  return $ Co (Lo.CInstance x v witnesses)
              (\ decode -> do
                    ws <- readRef witnesses
                    mapM decode ws)

--------------------------------------------------------------------------

-- Constraint abstractions -

-- The [CDef] form is so trivial that it deserves its own syntax. Viewing it
-- as a special case of [CLet] would be more costly (by a constant factor). 

def :: TermVar -> Var m (Src t) -> Co m t a -> Co m t a
def x v (Co rc k) = Co (Lo.CDef x v rc) k

-- The general form of [CLet] involves two constraints, the left-hand side and
-- the right-hand side, yet it defines a *family* of constraint abstractions,
-- bound to the term variables [xs].

data Letn t a b  = Letn { genvars :: [Int],
                          rhs     :: a,
                          rhs_ty  :: [([Int],t)],
                          body    :: b }
  

{-
letn :: (MonadFresh m, MonadRef m, Output t) =>
        [TermVar]
        -> ([Var m (Src t)] -> m (Co m t a))
        -> Co m t b
        -> m (Co m t ([Int], a, [ ([Int],t) ], b))
-}
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

  liftIO $ putStrLn $ "new constraint:" ++ (show raw_co)
  
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
        return (generalizable, a, ss, b))
{-
let1 :: (MonadFresh m, MonadRef m, Output t) =>
        TermVar
        -> (Var m (Src t) -> m (Co m t a))
        -> Co m t b
        -> m (Co m t ([Int], a, ([Int],t), b))
-}
let1 x f1 c2 = do
  c <- letn [ x ] (\ [x] -> f1 x) c2
  return $ fmap
    (\(generalizable, v1, [ss], v2) ->
               (generalizable, v1, ss, v2)) c
  
{-  
let0 :: (MonadFresh m, MonadRef m, Output t) =>
        Co m t a ->
        m (Co m t ([Int], a))
-}
let0 c1 = do
  letn [] (\ _ -> return c1) (pure ())
    <>
    (\ (generalizable, v1, _, ()) ->
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
             
solve :: forall m t ra a.
         (ZipM (Src t), Typeable (Src t), MonadFresh m, MonadEqRef m,
          MonadCatch m, Typeable m, Typeable t, Show t, MonadIO m,
          MArray ra [Var m (Src t)] m,
          Show ((Src t) (Var m (Src t))), 
          Output t) =>
         Proxy ra -> Bool -> Co m t a  -> m a
solve p rectypes (Co rc k) = do
  Lo.solve p rectypes rc
    `catch` (\ (e :: U.Err m (Src t)) ->
              case e of
                (U.Unify v1 v2) -> do
                  decode <- (Lo.new_decoder :: m (Lo.Decoder m t))
                  t1 <- decode v1
                  t2 <- decode v2
                  (throwM (Unify t1 t2))
                (U.Cycle v)     -> do
                  decode <- (Lo.new_decoder :: m (Lo.Decoder m t))
                  t <- decode v
                  (throwM (Cycle t)))
  decode <- Lo.new_decoder 
  k decode
  
        
    

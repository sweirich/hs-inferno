module TypeInf where

import Control.Monad.Except
import Control.Applicative

import Data.IORef

-- from union-find package
-- import Control.Monad.Trans.UnionFind

-- type variables
type Var     = Int

data Type = IntTy 
     | BoolTy 
     | FunTy Type Type       -- i.e. t1 -> t2
     | VarTy Var             -- i.e. type 'a'
    deriving (Eq, Show)

type TermVar = String

data Bop = Plus | Times | Minus deriving (Eq, Ord, Show)

data Expression =
   Var TermVar                  
 | IntExp  Int                       
 | BoolExp Bool
 | Op  Bop Expression Expression
 | If Expression Expression Expression
 | Fun TermVar Expression                 -- anonymous function,   'fun x -> e'
 | App Expression Expression              -- function application, 'e1 e2'
 | LetRec TermVar Expression Expression  -- (recursive) binding,  'let rec f = e in e'
    deriving (Show, Eq)


-- unifier



{-


type IScheme = String

type Decoder = Var -> Type
type Env = Decoder

newtype Co a = Co (RawCo, Env -> a)



data RawCo =
  | CTrue
  | CConj RawCo RawCo
  | CEq Var Var
  | CExist Var RawCo
  | CInstance TermVar Var (IORef [Var])
  | CDef TermVar Var RawCo
  | CLet [ (TermVar, Var, IORef IScheme) ]
         RawCo
         RawCo
         (IORef [Var])

data Err =
  | Unbound TermVar
  | Unify Var Var
  | Cycle Var

data SolverM = ErrorM Err IO

solve :: Bool -> RawCo -> SolverM ()
solve = undefined

decode_variable :: Var -> SolverM ()
decode_variable = undefined
-}

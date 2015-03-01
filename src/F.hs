module F where

import SolverHi (TermVar)

data Ty b a =
    TyVar a
  | TyBool
  | TyArrow    (Ty a b) (Ty a b)
  | TyProduct  (Ty a b) (Ty a b)
  | TyForall b (Ty a b)
  | TyMu b     (Ty b a)
  -- skip rectypes for now
    deriving (Eq, Show)
             
type NominalType = Ty Int Int

data Tm b a =
    Var TermVar
  | Abs TermVar (Ty b a) (Tm b a)
  | App (Tm b a) (Tm b a)
  | Let TermVar (Tm b a) (Tm b a)
  | TyAbs b (Tm b a)
  | TyApp (Tm b a) (Ty b a)
  | Pair (Tm b a) (Tm b a)
  | Proj Int (Tm b a)
  | Bool Bool
  | If (Tm b a) (Tm b a) (Tm b a)
    deriving (Eq, Show)

type NominalTerm = Tm Int Int

ftyabs :: [b] -> Tm b a -> Tm b a
ftyabs []     t = t
ftyabs (v:vs) t = TyAbs v (ftyabs vs t)

ftyapp :: Tm b a -> [Ty b a] -> Tm b a
ftyapp t [] = t
ftyapp t (v:vs) = ftyapp (TyApp t v) vs

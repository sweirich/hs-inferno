{-# LANGUAGE DeriveDataTypeable #-}
module ML where

import Data.Typeable
import Language.Inferno.SolverHi (TermVar)

data Tm = Var TermVar
        | Abs TermVar Tm
        | App Tm Tm
        | Let TermVar Tm Tm
        | Pair Tm Tm
        | Proj Int Tm
        | Bool Bool
        | If Tm Tm Tm
       deriving (Typeable, Show)

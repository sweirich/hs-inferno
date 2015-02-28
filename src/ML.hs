{-# LANGUAGE DeriveDataTypeable #-}
module ML where

import Data.Typeable
import SolverHi (TermVar)

data Tm = Var TermVar
        | Abs Tm Tm
        | App Tm Tm
        | Let TermVar Tm Tm
       deriving(Typeable, Show)

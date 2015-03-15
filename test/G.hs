{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE NoImplicitPrelude #-}

module G where

import Prelude hiding ((^^),abs)

import Control.Applicative
import Control.Monad

import Language.Inferno.Solver

import Text.PrettyPrint (Doc)
import qualified Text.PrettyPrint as PP

---------------------------------------
-- Language syntax for types and terms
data Ty a =
    TyVar Int         -- nominal 
  | TyBool
  | TyArrow    a   a 
  | TyProduct  a   a 
  | TyForall   Int a  -- nominal
  | TyEx              -- unification variables
  -- skip rectypes for now
    deriving (Eq, Show, Functor, Foldable, Traversable, Typeable)            

data Mu f = Roll (f (Mu f))
    deriving (Typeable)
             
type Type = Mu Ty

type Annot = Maybe Type

data Tm  =
    Var TermVar
  | Abs TermVar Annot Tm 
  | App Tm Tm
  | Let TermVar Annot Tm Tm
  | TyAbs Int Tm
  | TyApp Tm Type 
  | Pair  Tm Tm
  | Proj Int Tm 
  | Bool Bool
  | If Tm Tm Tm
    deriving (Eq, Show)

---------------------------------
instance Eq Type where
  (Roll x) == (Roll y) = x == y
instance Show Type where
  show (Roll x) = show x
---------------------------------

-- Pretty printing code

-- lefty :: (Pretty a, Pretty b, Pretty c) => Int -> a -> b -> Doc -> c -> Doc
lefty p e a op b
  | p < q     = PP.parens (ppPrec q e)
  | otherwise = ppPrec q a PP.<+> op PP.<+> special q b
  where q = prec e

-- righty :: Pretty a => Int -> a -> a -> Doc -> a -> Doc
righty p e a op b
  | p < q     = PP.parens (ppPrec q e)
  | otherwise = special q a PP.<+> op PP.<+> ppPrec q b
  where q = prec e

altrighty p e a op b
  | p < q     = PP.parens (ppPrec q e)
  | otherwise = ppPrec (q-1) a PP.<+> op PP.<+> ppPrec q b
  where q = prec e


-- special :: Pretty a => Int -> a -> Doc
special p e
  | p == prec e = PP.parens (ppPrec p e)
  | otherwise   = ppPrec p e

-- prefix :: Pretty a => Int -> a -> Doc -> a -> Doc
prefix p e op a
  | p < q     = PP.parens (ppPrec q e)
  | otherwise = op PP.<> special q a
 where q = prec e


postfix p e a op
  | p < q     = PP.parens (ppPrec q e)
  | otherwise = special q a PP.<> op
 where q = prec e
           

instance Pretty Int where
  prec k = 0
  ppPrec _ = PP.int 
instance Pretty String where
  prec k = 0
  ppPrec _ = PP.text


instance Pretty a => Pretty (Ty a) where
  prec (TyVar _) = 0
  prec (TyBool)  = 0
  prec (TyForall _ _)  = 8
  prec (TyProduct _ _)  = 4
  prec (TyArrow _ _) = 6
  prec (TyEx)    = 0
  
  ppPrec p ty =
    case ty of
     (TyVar k)       -> pp k
     (TyBool )       -> PP.text "Bool"
     (TyEx)          -> PP.text "_"
     (TyArrow t1 t2) ->
       altrighty p ty t1 (PP.text "->") t2
     (TyProduct t1 t2) ->
       PP.parens (PP.cat [pp t1, PP.text ",", pp t2])
     (TyForall k t1) ->
       prefix p ty (PP.text "forall" PP.<+> PP.int k PP.<> PP.text ".") t1

instance Pretty (Mu Ty) where
  ppPrec p (Roll t) = ppPrec p t

  

instance Pretty Tm where
  prec (Var _)     = 0
  prec (Bool _)    = 0
  prec (App _ _)   = 3
  prec (TyApp _ _) = 3
  prec (Abs _ _ _) = 5
  prec (TyAbs _ _) = 5
  prec (Proj _ _)  = 5
  prec (Let _ _ _ _) = 5
  prec (If _ _ _)  = 5
  prec (Pair _ _)  = 11

  ppPrec p tm = let q = prec tm in
    (if p < q then PP.parens else id) $
    case tm of
    (Var x)  -> PP.text x
    (Bool b) -> PP.text (show b)
    (App t1 t2) ->
      PP.sep [ppPrec q t1, ppPrec (q-1) t2]
    (TyApp t1 t2) ->
      PP.sep [ppPrec q t1, PP.brackets (pp t2)]
    (Abs x mty t1) ->
      PP.hang (PP.char '\\' PP.<+> pp x PP.<+> ppAnnot mty PP.<> PP.text ".")
            2 (ppPrec q t1)
    (TyAbs x t1) -> 
      PP.hang (PP.text "/\\" PP.<+> pp x PP.<> PP.text ".")
            2 (ppPrec q t1)
    (Proj i t1)  ->
      ppPrec q t1 PP.<> PP.text "." PP.<> PP.int i
    (Pair t1 t2) ->
      pp t1 PP.<> PP.text "," PP.<+> pp t2
    (Let x mty t1 t2) ->
      PP.hang (PP.text "let" PP.<+> pp x PP.<> ppAnnot mty PP.<+> PP.text "="
               PP.<+> pp t1 PP.<+> PP.text "in")
         2 (ppPrec q t2)
    (If t1 t2 t3) ->
      PP.sep [PP.text "if", pp t1, PP.text "then", pp t2, PP.text "else", pp t3]

ppAnnot Nothing = PP.empty
ppAnnot (Just ty) = PP.colon PP.<+> pp ty

--------------------------------------------------------------------------

instance ZipM Ty where
  zipM_ f (TyVar i) (TyVar j) | i == j = return ()
  zipM_ f TyBool TyBool                = return ()
  zipM_ f (TyArrow t1 t2) (TyArrow u1 u2) = do
    f t1 u1
    f t2 u2
  zipM_ f (TyProduct t1 t2) (TyProduct u1 u2) = do
    f t1 u1
    f t2 u2
  -- not so great! bound variables must be the same
  zipM_ f (TyForall i t) (TyForall j u) | i == j = f t u  
  zipM_ f t1 t2 = throwM $ ZipError t1 t2

  zipM _ = error "undefined"


instance Output Type where
  type Src Type = Ty

  tovar = Roll . TyVar
  struc = Roll


--------------------------------------------------------------------------    

product_i 1 t u = TyProduct t u
product_i 2 t u = TyProduct u t

fty :: [Int] -> Type -> Type
fty [] ty     = ty
fty (v:vs) ty = Roll (TyForall v (fty vs ty))


ftyabs :: [Int] -> Tm -> Tm 
ftyabs []     t = t
ftyabs (v:vs) t = TyAbs v (ftyabs vs t)

ftyapp :: Tm -> [Type] -> Tm
ftyapp t [] = t
ftyapp t (v:vs) = ftyapp (TyApp t v) vs


-- smart constructor for let
flet x (Var y) u | x == y = u
flet x t u = Let x Nothing t u

-- eta-reducing smart constructor for type abstraction
ftyabs1 v (TyApp t (Roll (TyVar w))) | v == w = t
ftyabs1 v t = TyAbs v t

--------------------------------------------------------------------------

-- The unifier


type C = Co Type Tm

type Variable = Var Ty

-- For type annotations in the source language:
-- Introduce an existential variable, defined to be equal
-- to a given type.
-- Any occurrence of TyEx creates an unconstrained variable
existsTy :: Mu Ty -> (Variable -> M (Co Type a)) -> M (Co Type a)
existsTy (Roll ty) f =
  case ty of
    TyEx    -> exist_ f
    TyVar i -> exist_aux_ (Just (TyVar i)) f
    TyBool  -> exist_aux_ (Just TyBool) f 
    TyArrow t1 t2 ->
      existsTy t1 (\ v1 ->
      existsTy t2 (\ v2 ->
      exist_aux_ (Just (TyArrow v1 v2)) f))
    TyProduct t1 t2 ->
      existsTy t1 (\ v1 ->
      existsTy t2 (\ v2 ->
      exist_aux_ (Just (TyProduct v1 v2)) f))
    TyForall i t -> 
      existsTy t (\ v ->
      exist_aux_ (Just (TyForall i v)) f)

--------------------------------------------------------------------------  

hastype :: Tm -> Variable -> M C
hastype (Var x) tau = do
  c <- (inst x tau)
  return $ fmap (\vs -> ftyapp (Var x) vs) c

  
hastype (Abs x Nothing u) tau = do
  c <- exist (\ v1 ->
          exist (\ v2 -> do
                  c1 <- tau -==- TyArrow v1 v2
                  c2 <- hastype u v2
                  return (c1 ^& def x (trivial v1) c2)))
  return $ fmap (\ (tau1, (tau2, ((), u))) -> Abs x (Just tau1) u) c
  
hastype (Abs x (Just t) u) tau = do
  c <- existsTy t (\ v1 ->
          exist (\ v2 -> do
                  c1 <- tau -==- TyArrow v1 v2
                  c2 <- hastype u v2
                  return (pure t ^& c1 ^& def x (trivial v1) c2)))
  return $ fmap (\ (tau1, (tau2, u)) -> Abs x (Just tau1) u) c

hastype (App t1 t2) tau = do
  c <- exist_ (\v -> do
               c1 <- liftS hastype t1 (TyArrow v tau)
               c2 <- hastype t2 v
               return $ c1 ^& c2)
  return $ fmap (\ (t1', t2') -> App t1' t2') c

hastype (Let x Nothing t u) tau = do
  -- construct a (recursive) let constraint
  cu <- hastype u tau
  c  <- let1 True x (hastype t) cu
  return $ fmap (\ (a, t', (b, ty), u') ->
                  Let x (Just (fty a ty)) (ftyabs a t') u') c

-- recursive, non-generalizing (annotated) let
hastype (Let x (Just ty) t u) tau = do
  c <- existsTy ty (\v -> do
                     cu  <- hastype u tau
                     ct  <- hastype t v
                     return (def x (trivial v) (cu ^& ct)))
  return $ fmap (\ (u', t') ->
                  Let x (Just ty) t' u') c


hastype (Pair t1 t2) tau = do
  c <- exist_ (\ v1 ->
         exist_ (\ v2 -> do
            -- [tau] must be the product type [v1 * v2]
            c1 <- tau -==- TyProduct v1 v2
            c2 <- hastype t1 v1
            c3 <- hastype t2 v2
            return $ c1 ^^ c2 ^& c3))
  return $ fmap (\ (t1, t2) -> Pair t1 t2) c
  
hastype (Proj i t) tau =  do
  c <- exist_ (\ other -> 
         liftS hastype t (product_i i tau other))
  return $ fmap (\t -> Proj i t) c

hastype (Bool b) tau = do
  c <- tau -==- TyBool
  return $ fmap (\ () -> Bool b) c

hastype (If e1 e2 e3) tau = do
  c1 <- liftS hastype e1 TyBool
  c2 <- hastype e2 tau
  c3 <- hastype e3 tau
  return $ fmap (\ ((t1,t2),t3) ->
                  If t1 t2 t3) (c1 ^& c2 ^& c3)

--------------------------------------------------------------------------
constraints t = do
  c  <- exist_ (hastype t)
  c2 <- let0 c
  return $ fmap (\(vs,t) -> ftyabs vs t) c2
  

translate t = do
  c3 <- constraints t
  solve False c3

inf :: Tm -> IO Tm
inf t = runSolverM (translate t)


--------------------------------------------------------------------------

abs x = Abs x Nothing


ml1 = abs "x" (Var "x")

ml2 = abs "f" (abs "x"
      (App (Var "f") (Var "x")))

ml3 = Let "id" Nothing ml1
       (Pair (App (Var "id") (Bool True))
        (App (Var "id") (Pair (Bool True) (Bool False))))
       
ml4 = Let "id1" Nothing ml1
      (Let "id2" Nothing  ml2 
       (Pair (App (Var "id1") (Bool True))
        (App (Var "id2") (Pair (Bool True) (Bool False)))))

ml5 = Let "id1" Nothing ml1
      (Let "id2" Nothing  ml1 
       (Pair (App (Var "id1") (Bool True))
        (App (Var "id2") (Pair (Bool True) (Bool False)))))


bool = Roll TyBool
t1 --> t2 = Roll (TyArrow t1 t2)

x =
  Var "x"

y =
  Var "y"

mlid =
  abs "x" x

-- needs rectypes
delta =
  abs "x" (App x x)

deltadelta =
  App delta delta

idid =
  App mlid mlid

k =
  abs "x" (abs "y" x)

genid =
  Let "x" Nothing mlid x

genidid =
  Let "x" Nothing mlid (App x x)

genkidid =
  Let "x" Nothing (App k mlid) (App x mlid)

genkidid2 =
  Let "x" Nothing (App (App k mlid) mlid) x

app_pair = -- ill-typed 
  App (Pair mlid mlid) mlid

mlnot = abs "x" (If x (Bool False) (Bool True))

reclet =
  Let "f" Nothing (Abs "x" Nothing (App (Var "f") (Var "x"))) (Var "f")

annlet =
  Let "f" (Just (Roll (TyArrow (Roll TyBool) (Roll TyBool))))
          (Abs "x" Nothing (App (Var "f") (Var "x")))
      (App (Var "f") (Bool True))

annlet2 =
  Let "f" (Just (Roll (TyArrow (Roll TyEx) (Roll TyEx))))
          (Abs "x" Nothing (App (Var "f") (Var "x")))
      (App (Var "f") (Bool True))

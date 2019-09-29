module Term where

import Data.Char
import Data.Maybe
import Data.List
import Data.Foldable
import Control.Monad
import Text.PrettyPrint.HughesPJ as P
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import qualified Text.ParserCombinators.Parsec.Token as T
import Text.ParserCombinators.Parsec.Language
import Debug.Trace
import System.IO
import System.Directory


data Term = Free String -- free variable
          | Bound Int -- bound variable with de Bruijn index
          | Lambda String Term -- lambda abstraction
          | Con String [Term] -- constructor application
          | Fun String -- function call
          | Apply Term [Term] -- application
          | Case Term [(String,[String],Term)] -- case expression
          | Let String Term Term -- temporary let expression
          | Letrec String [String] Term Term -- local function

instance Show Term where
   show t = render $ prettyTerm t

type Prog = (Term,[(String,([String],Term))])

showProg p = render $ prettyProg p

-- equality of terms

instance Eq Term where
   (==) t t' = eqTerm [] [] (t,t')

eqTerm s1 s2 (Free x,t) | x `elem` fst(unzip s1) = eqTerm [] [] (instantiate s1 (Free x),instantiate s2 t)
eqTerm s1 s2 (Free x,Free x') = x==x'
eqTerm s1 s2 (Bound i,Bound i') = i==i'
eqTerm s1 s2 (Lambda x t,Lambda x' t') = eqTerm s1 s2 (t,t')
eqTerm s1 s2 (Con c ts,Con c' ts') | c==c' = all (eqTerm s1 s2) (zip ts ts')
eqTerm s1 s2 (Fun f,Fun f') = f==f'
eqTerm s1 s2 (Apply (Bound i) ts,Apply (Bound i') ts') = i==i'
eqTerm s1 s2 (Apply t ts,Apply t' ts') = eqTerm s1 s2 (t,t') && all (eqTerm s1 s2) (zip ts ts')
eqTerm s1 s2 (Case t bs,Case t' bs') | match bs bs' = eqTerm s1 s2 (t,t') && all (\((_,_,t),(_,_,t')) -> eqTerm s1 s2 (t,t')) (zip bs bs')
eqTerm s1 s2 (Let x t u,Let x' t' u') = eqTerm s1 s2 (t,t') && eqTerm s1 s2 (u,u')
eqTerm s1 s2 (Letrec f xs t u,Letrec f' xs' t' u') = eqTerm (zip xs (args (instantiate s1 u))) (zip xs' (args (instantiate s2 u'))) (foldr concrete t xs,foldr concrete t' xs')
eqTerm s1 s2 (t,t') = False

-- context surrounding redex

data Context = EmptyCtx
             | ApplyCtx Context [Term]
             | CaseCtx Context [(String,[String],Term)]

-- place term in context

place t EmptyCtx = t
place t (ApplyCtx k ts) = place (Apply t ts) k
place t (CaseCtx k bs) = place (Case t bs) k

match bs bs' = length bs == length bs' && all (\((c,xs,t),(c',xs',t')) -> c == c' && length xs == length xs') (zip bs bs')

-- checking for renaming

renaming t u = renaming' [] [] t u []

renaming' s1 s2 (Free x) t r | x `elem` fst(unzip s1) = renaming' [] [] (instantiate s1 (Free x)) (instantiate s2 t) r
renaming' s1 s2 (Free x) (Free x') r = if x `elem` fst (unzip r)
                                       then if (x,x') `elem` r then Just r else Nothing
                                       else Just ((x,x'):r)
renaming' s1 s2 (Bound i) (Bound i') r | i==i' = Just r
renaming' s1 s2 (Lambda _ t) (Lambda _ t') r = renaming' s1 s2 t t' r
renaming' s1 s2 (Con c ts) (Con c' ts') r | c==c' = foldrM (\(t,t') r -> renaming' s1 s2 t t' r) r (zip ts ts')
renaming' s1 s2 (Fun f) (Fun f') s | f==f' = Just s
renaming' s1 s2 (Apply (Bound i) ts) (Apply (Bound i') ts') r | i==i' = Just r
renaming' s1 s2 (Apply t ts) (Apply t' ts') r = renaming' s1 s2 t t' r >>= (\r -> foldrM (\(t,t') r -> renaming' s1 s2 t t' r) r (zip ts ts'))
renaming' s1 s2 (Case t bs) (Case t' bs') r | match bs bs' = renaming' s1 s2 t t' r >>= (\r -> foldrM (\((_,_,t),(_,_,t')) r -> renaming' s1 s2 t t' r) r (zip bs bs'))
renaming' s1 s2 (Let x t u) (Let x' t' u') r = renaming' s1 s2 t t' r >>= renaming' s1 s2 u u'
renaming' s1 s2 (Letrec f xs t u) (Letrec f' xs' t' u') r = renaming' (zip xs (args (instantiate s1 u))) (zip xs' (args (instantiate s2 u'))) (foldr concrete t xs) (foldr concrete t' xs') r
renaming' s1 s2 t t' r = Nothing

-- checking for instance

inst t u = inst' [] [] t u []

inst' s1 s2 (Free x) t s | x `elem` fst(unzip s1) = inst' [] [] (instantiate s1 (Free x)) (instantiate s2 t) s
inst' s1 s2 (Free x) t s = if x `elem` fst (unzip s)
                           then if (x,t) `elem` s then Just s else Nothing
                           else Just ((x,t):s)
inst' s1 s2 (Bound i) (Bound i') s | i==i' = Just s
inst' s1 s2 (Lambda x t) (Lambda x' t') s = inst' s1 s2 t t' s
inst' s1 s2 (Con c ts) (Con c' ts') s | c==c' = foldrM (\(t,t') s -> inst' s1 s2 t t' s) s (zip ts ts')
inst' s1 s2 (Fun f) (Fun f') s | f==f' = Just s
inst' s1 s2 (Apply (Bound i) ts) (Apply (Bound i') ts') s | i==i' = Just s
inst' s1 s2 (Apply t ts) (Apply t' ts') s = inst' s1 s2 t t' s >>= (\s -> foldrM (\(t,t') s -> inst' s1 s2 t t' s) s (zip ts ts'))
inst' s1 s2 (Case t bs) (Case t' bs') s | match bs bs' = inst' s1 s2 t t' s >>= (\s -> foldrM (\((_,_,t),(_,_,t')) s -> inst' s1 s2 t t' s) s (zip bs bs'))
inst' s1 s2 (Let x t u) (Let x' t' u') s = inst' s1 s2 t t' s >>= inst' s1 s2 u u'
inst' s1 s2 (Letrec f xs t u) (Letrec f' xs' t' u') s = inst' (zip xs (args (instantiate s1 u))) (zip xs' (args (instantiate s2 u'))) (foldr concrete t xs) (foldr concrete t' xs') s
inst' s1 s2 t t' s = Nothing

-- checking for embedding for generalisation

embed t u = couple [] [] t u []

embedding s1 s2 t u r = couple s1 s2 t u r ++ dive s1 s2 t u r

couple s1 s2 (Free x) (Free x') r | x `elem` fst(unzip s1) && x' `elem` fst(unzip s2) = embedding [] [] (instantiate s1 (Free x)) (instantiate s2 (Free x')) r
couple s1 s2 (Free x) (Free x') r = if x `elem` fst (unzip r)
                                    then [r | (x,x') `elem` r]
                                    else [(x,x'):r]
couple s1 s2 (Bound i) (Bound i') r | i == i' = [r]
couple s1 s2 (Lambda x t) (Lambda x' t') r = embedding s1 s2 t t' r
couple s1 s2 (Con c ts) (Con c' ts') r | c==c' = foldr (\(t,t') rs -> concat [embedding s1 s2 t t' r | r <- rs]) [r] (zip ts ts')
couple s1 s2 (Fun f) (Fun f') r | f==f' = [r]
couple s1 s2 (Apply (Bound i) ts) (Apply (Bound i') ts') r | i==i' = [r]
couple s1 s2 (Apply t ts) (Apply t' ts') r = foldr (\(t,t') rs -> concat [embedding s1 s2 t t' r | r <- rs]) (embedding s1 s2 t t' r) (zip ts ts')
couple s1 s2 (Case t bs) (Case t' bs') r | match bs bs' = foldr (\((c,xs,t),(c',xs',t')) rs -> concat [embedding s1 s2 t t' r | r <- rs]) (embedding s1 s2 t t' r) (zip bs bs')
couple s1 s2 (Let x t u) (Let x' t' u') r  = concat [embedding s1 s2 u u' r' | r' <- embedding s1 s2 t t' r]
couple s1 s2 (Letrec f xs t u) (Letrec f' xs' t' u') r = couple (zip xs (args (instantiate s1 u))) (zip xs' (args (instantiate s2 u'))) (foldr concrete t xs) (foldr concrete t' xs') r
couple s1 s2 t t' r = []

dive s1 s2 t (Lambda x t') r = embedding s1 s2 t (concrete x t') r
dive s1 s2 t (Con c ts) r = concat [embedding s1 s2 t t' r | t' <- ts]
dive s1 s2 t (Apply t'  ts) r = embedding s1 s2 t t' r ++ concat [embedding s1 s2 t u r | u <- ts]
dive s1 s2 t (Case t' bs) r = embedding s1 s2 t t' r ++ concatMap (\(c,xs,t') -> embedding s1 s2 t (foldr concrete t' xs) r) bs
dive s1 s2 t (Let x t' u) r = embedding s1 s2 t t' r ++ embedding s1 s2 t (concrete x u) r
dive s1 s2 t (Letrec f xs t' u) r = embedding s1 s2 t u r ++ embedding s1 s2 t (foldr concrete t' xs) r
dive s1 s2 t t' r = []

-- most specific generalisation of terms

generalise t u = generalise' [] [] t u (free t ++ free u) [] [] []

generalise' s1 s2 (Free x) t fv bv g1 g2 | x `elem` fst(unzip s1) = let (t',g1',g2') = generalise' [] [] (instantiate s1 (Free x)) (instantiate s2 t) fv bv g1 g2
                                                                    in  case t' of
                                                                           Free x' -> (Free x,(x,fromJust (lookup x' g1')):g1,(x,fromJust (lookup x' g2')):g2)
                                                                           _ -> (t',g1',g2')
generalise' s1 s2 (Free x) (Free x') fv bv g1 g2 | x==x' = (Free x,g1,g2)
generalise' s1 s2 (Bound i) (Bound i') fv bv g1 g2 | i==i' = (Bound i,g1,g2)
generalise' s1 s2 (Lambda x t) (Lambda x' t') fv bv g1 g2 = let x'' = rename (fv++fst(unzip (s2++g2))) x
                                                                (t'',g1',g2') = generalise' s1 s2 (concrete x'' t) (concrete x'' t') (x'':fv) (x'':bv) g1 g2
                                                            in  (Lambda x (abstract t'' x''),g1',g2')
generalise' s1 s2 (Con c ts) (Con c' ts') fv bv g1 g2 | c==c' = let ((g1',g2'),ts'') = mapAccumL (\(g1,g2) (t,t') -> let (t'',g1',g2') = generalise' s1 s2 t t' fv bv g1 g2
                                                                                                                     in  ((g1',g2'),t'')) (g1,g2) (zip ts ts')
                                                                in  (Con c ts'',g1',g2')
generalise' s1 s2 (Fun f) (Fun f') fv bv g1 g2 | f==f' = (Fun f,g1,g2)
generalise' s1 s2 (Apply (Free x) ts) (Apply (Free x') ts') fv bv g1 g2 | x `elem` bv && x==x' = (Apply (Free x) ts,g1,g2)
generalise' s1 s2 (Apply t ts) (Apply t' ts') fv bv g1 g2 | not (null (embed t t')) = let (t'',g1',g2') = generalise' s1 s2 t t' fv bv g1 g2
                                                                                          ((g1'',g2''),ts'') = mapAccumL (\(g1,g2) (t,t') -> let (t'',g1',g2') = generalise' s1 s2 t t' fv bv g1 g2
                                                                                                                                             in  ((g1',g2'),t'')) (g1',g2') (zip ts ts')
                                                                                      in  (Apply t'' ts'',g1'',g2'')
generalise' s1 s2 (Case t bs) (Case t' bs') fv bv g1 g2 | match bs bs' = let (t'',g1',g2') = generalise' s1 s2 t t' fv bv g1 g2
                                                                             ((g1'',g2''),bs'') = mapAccumL (\(g1,g2) ((c,xs,t),(c',xs',t')) -> let fv' = foldr (\x fv -> let x' = rename (fv++fst(unzip (s2++g2))) x in x':fv) fv xs
                                                                                                                                                    xs'' = take (length xs) fv'
                                                                                                                                                    (t'',g1',g2') = generalise' s1 s2 (foldr concrete t xs'') (foldr concrete t' xs'') fv' (xs''++bv) g1 g2
                                                                                                                                                in ((g1',g2'),(c,xs,foldl abstract t'' xs''))) (g1',g2') (zip bs bs')
                                                                         in  (Case t'' bs'',g1'',g2'')
generalise' s1 s2 (Let x t u) (Let x' t' u') fv bv g1 g2 = let x'' = rename (fv++fst(unzip (s2++g2))) x
                                                               (t'',g1',g2') = generalise' s1 s2 t t' fv bv g1 g2
                                                               (u'',g1'',g2'') = generalise' s1 s2 (concrete x'' u) (concrete x'' u') fv bv g1' g2'
                                                            in  (Let x t'' (abstract u'' x''),g1'',g2'')
generalise' s1 s2 (Letrec f xs t u) (Letrec f' xs' t' u') fv bv g1 g2 | not (null rs) = let xs1 = [renameVar (head rs) x | x <- xs]
                                                                                            (t'',g1',g2') = generalise' (zip xs1 (args (instantiate s1 u))) (zip xs2 (args (instantiate s2 u'))) (foldr concrete t (x:xs1)) (foldr concrete t' (x:xs2)) (x:xs1++fv) (x:xs1++bv) g1 g2
                                                                                        in (Letrec f xs1 (foldl abstract t'' (x:xs1)) (Apply (Bound 0) (map Free xs1)),g1',g2')
   where x:fv' = foldr (\x fv -> let x' = rename (fv++fst(unzip (s2++g2))) x in x':fv) fv (f:xs')
         xs2 = take (length xs') fv'
         rs = embed (foldr concrete t xs) (foldr concrete t' xs2)
generalise' s1 s2 t u fv bv g1 g2 = let xs = intersect (free t) bv
                                        t' = instantiate s1 (foldl (\t x -> Lambda x (abstract t x)) t xs)
                                        u' = instantiate s2 (foldl (\t x -> Lambda x (abstract t x)) u xs)
                                    in  case find (\(x,t) -> t==t' && (lookup x g2 == Just u')) g1 of
                                           Just (x,t) -> (makeApplication (Free x) (map Free xs),g1,g2)
                                           Nothing -> let x = rename (fv++fst(unzip (s2++g2))) "x"
                                                      in  (makeApplication (Free x) (map Free xs),(x,t'):g1,(x,u'):g2)

makeLet s t = foldl (\u (x,t) -> Let x t (abstract u x)) t s

makeApplication t [] = t
makeApplication t ts = Apply t ts

eval t (ApplyCtx k []) d r a = eval t k d r a
eval (Free x) k d r a = error ("Unbound identifier: "++x)
eval (Lambda x t) EmptyCtx d r a = (Lambda x t,r,a)
eval (Lambda x t) (ApplyCtx k (t':ts)) d r a = eval (subst t' t) (ApplyCtx k ts) d (r+1) a
eval (Lambda x t) (CaseCtx k bs) d r a = error ("Unapplied function in case selector: " ++ show (Lambda x t))
eval (Con c ts) EmptyCtx d r a = let ((r',a'),ts') = mapAccumL (\(r,a) t -> let (t',r',a') = eval t EmptyCtx d r a
                                                                            in  ((r',a'),t')) (r,a) ts
                                 in  (Con c ts',r'+1,a'+1)
eval (Con c ts) (ApplyCtx k ts') d r a = error ("Constructor application is not saturated: "++show (place (Con c ts) (ApplyCtx k ts')))
eval (Con c ts) (CaseCtx k bs) d r a = case find (\(c',xs,t) -> c==c' && length xs == length ts) bs of
                                          Nothing -> error ("No matching pattern in case for term:\n\n"++show (Case (Con c ts) bs))
                                          Just (c',xs,t) -> eval (foldr subst t ts) k d (r+length ts) a
eval (Fun f) k d r a = case lookup f d of
                          Nothing -> error ("Undefined function: " ++ f)
                          Just (xs,t) -> eval (foldr (\x t->Lambda x (abstract t x)) t xs) k d (r+1) a
eval (Apply t ts) k d r a = eval t (ApplyCtx k ts) d r a
eval (Case t bs) k d r a = eval t (CaseCtx k bs) d r a
eval (Let x t u) k d r a = eval (subst t u) k d (r+1) a
eval (Letrec f xs t u) k d r a = let f' = rename (fst (unzip d)) f
                                     t' = concreteFun f' (foldr concrete t xs)
                                     u' = concreteFun f' u
                                 in  eval u' k ((f',(xs,t')):d) (r+1) a

-- free variables in a term

free t = free' t []

free' (Free x) xs = if x `elem` xs then xs else x:xs
free' (Bound i) xs = xs
free' (Lambda x t) xs = free' t xs
free' (Con c ts) xs = foldr free' xs ts
free' (Fun f) xs = xs
free' (Apply t ts) xs = foldr free' (free' t xs) ts
free' (Case t bs) xs = foldr (\(_,_,t) xs -> free' t xs) (free' t xs) bs
free' (Let x t u) xs = free' t (free' u xs)
free' (Letrec f xs' t u) xs = free' t (free' u xs)

-- functions in a program

funs = funs' []

funs' fs (Free x) = fs
funs' fs (Bound i) = fs
funs' fs (Lambda x t) = funs' fs t
funs' fs (Con c ts) = foldl funs' fs ts
funs' fs (Apply t ts) = foldl funs' (funs' fs t) ts
funs' fs (Fun f) = if f `elem` fs then fs else (f:fs)
funs' fs (Case t bs) = foldl (\fs (c,xs,t) -> funs' fs t) (funs' fs t) bs
funs' fs (Let x t u) = funs' (funs' fs t) u
funs' fs (Letrec f xs t u) = funs' (funs' fs t) u

-- shift global de Bruijn indices by i, where current depth is d

shift = shift' 0

shift' d 0 u = u
shift' d i (Free x) = Free x
shift' d i (Bound i') = if i' >= d then Bound (i'+i) else Bound i'
shift' d i (Lambda x t) = Lambda x (shift' (d+1) i t)
shift' d i (Con c ts) = Con c (map (shift' d i) ts)
shift' d i (Fun f) = Fun f
shift' d i (Apply t ts) = Apply (shift' d i t) (map (shift' d i) ts)
shift' d i (Case t bs) = Case (shift' d i t) (map (\(c,xs,t) -> (c,xs,shift' (d+length xs) i t)) bs)
shift' d i (Let x t u) = Let x (shift' d i t) (shift' (d+1) i u)
shift' d i (Letrec f xs t u) = Letrec f xs (shift' (d+1+length xs) i t) (shift' (d+1) i u)

-- substitute term t for variable with de Bruijn index i

subst = subst' 0

subst' i t (Free x) = Free x
subst' i t (Bound i')
   | i'<i      = Bound i'
   | i'==i     = shift i t
   | otherwise = Bound (i'-1)
subst' i t (Lambda x t') = Lambda x (subst' (i+1) t t')
subst' i t (Con c ts) = Con c (map (subst' i t) ts)
subst' i t (Fun f) = Fun f
subst' i t (Apply t' ts) = Apply (subst' i t t') (map (subst' i t) ts)
subst' i t (Case t' bs) = Case (subst' i t t') (map (\(c,xs,u) -> (c,xs,subst' (i+length xs) t u)) bs)
subst' i t (Let x t' u) = Let x (subst' i t t') (subst' (i+1) t u)
subst' i t (Letrec f xs t' u) = Letrec f xs (subst' (i+1+length xs) t t') (subst' (i+1) t u)

-- instantiate a term t using substitution s

instantiate = instantiate' 0

instantiate' d s (Free x) = case lookup x s of
                               Just t  -> shift d t
                               Nothing -> Free x
instantiate' d s (Bound i) = Bound i
instantiate' d s (Lambda x t) = Lambda x (instantiate' (d+1) s t)
instantiate' d s (Con c ts) = Con c (map (instantiate' d s) ts)
instantiate' d s (Fun f) = Fun f
instantiate' d s (Apply t ts) = Apply (instantiate' d s t) (map (instantiate' d s) ts)
instantiate' d s (Case t bs) = Case (instantiate' d s t) (map (\(c,xs,t) -> (c,xs,instantiate' (d+length xs) s t)) bs)
instantiate' d s (Let x t u) = Let x (instantiate' d s t) (instantiate' (d+1) s u)
instantiate' d s (Letrec f xs t u) = Letrec f xs (instantiate' (d+1+length xs) s t) (instantiate' (d+1) s u)

-- replace variable x with de Bruijn index

abstract = abstract' 0

abstract' i (Free x') x = if x==x' then Bound i else Free x'
abstract' i (Bound i') x = if i'>=i then Bound (i'+1) else Bound i'
abstract' i (Lambda x' t) x = Lambda x' (abstract' (i+1) t x)
abstract' i (Con c ts) x = Con c (map (\t -> abstract' i t x) ts)
abstract' i (Fun f) x = Fun f
abstract' i (Apply t ts) x = Apply (abstract' i t x) (map (\t -> abstract' i t x) ts)
abstract' i (Case t bs) x = Case (abstract' i t x) (map (\(c,xs,t) -> (c,xs,abstract' (i+length xs) t x)) bs)
abstract' i (Let x' t u) x = Let x' (abstract' i t x) (abstract' (i+1) u x)
abstract' i (Letrec f xs t u) x = Letrec f xs (abstract' (i+1+length xs) t x) (abstract' (i+1) u x)

-- replace de Bruijn index 0 with variable x

concrete = concrete' 0

concrete' i x (Free x') = Free x'
concrete' i x (Bound i')
   | i'<i = Bound i'
   | i'==i = Free x
   | otherwise = Bound (i'-1)
concrete' i x (Lambda x' t) = Lambda x' (concrete' (i+1) x t)
concrete' i x (Con c ts) = Con c (map (concrete' i x) ts)
concrete' i x (Fun f) = Fun f
concrete' i x (Apply t ts) = Apply (concrete' i x t) (map (concrete' i x) ts)
concrete' i x (Case t bs) = Case (concrete' i x t) (map (\(c,xs,t) -> (c,xs,concrete' (i+length xs) x t)) bs)
concrete' i x (Let x' t u) = Let x' (concrete' i x t) (concrete' (i+1) x u)
concrete' i x (Letrec f xs t u) = Letrec f xs (concrete' (i+1+length xs) x t) (concrete' (i+1) x u)

-- replace function f with de Bruijn index

abstractFun = abstractFun' 0

abstractFun' i (Free x) f = Free x
abstractFun' i (Bound i') f = if i'>=i then Bound (i'+1) else Bound i'
abstractFun' i (Lambda x t) f = Lambda x (abstractFun' (i+1) t f)
abstractFun' i (Con c ts) f = Con c (map (\t -> abstractFun' i t f) ts)
abstractFun' i (Fun f') f = if f==f' then Bound i else Fun f'
abstractFun' i (Apply t ts) f = Apply (abstractFun' i t f) (map (\t -> abstractFun' i t f) ts)
abstractFun' i (Case t bs) f = Case (abstractFun' i t f) (map (\(c,xs,t) -> (c,xs,abstractFun' (i+length xs) t f)) bs)
abstractFun' i (Let x' t u) f = Let x' (abstractFun' i t f) (abstractFun' (i+1) u f)
abstractFun' i (Letrec f' xs t u) f = Letrec f' xs (abstractFun' (i+1+length xs) t f) (abstractFun' (i+1) u f)

-- replace de Bruijn index 0 with function f

concreteFun = concreteFun' 0

concreteFun' i f (Free x) = Free x
concreteFun' i f (Bound i')
   | i'<i = Bound i'
   | i'==i = Fun f
   | otherwise = Bound (i'-1)
concreteFun' i f (Lambda x t) = Lambda x (concreteFun' (i+1) f t)
concreteFun' i f (Con c ts) = Con c (map (concreteFun' i f) ts)
concreteFun' i f (Fun f') = Fun f'
concreteFun' i f (Apply t ts) = Apply (concreteFun' i f t) (map (concreteFun' i f) ts)
concreteFun' i f (Case t bs) = Case (concreteFun' i f t) (map (\(c,xs,t) -> (c,xs,concreteFun' (i+length xs) f t)) bs)
concreteFun' i f (Let x t u) = Let x (concreteFun' i f t) (concreteFun' (i+1) f u)
concreteFun' i f (Letrec f' xs t u) = Letrec f' xs (concreteFun' (i+1+length xs) f t) (concreteFun' (i+1) f u)

rename fv x = if   x `elem` fv
              then rename fv (x++"'")
              else x

-- rename a term t using renaming r

renameVar r x = fromMaybe x (lookup x r)

renameTerm r (Free x) = Free (renameVar r x)
renameTerm r (Bound i) = Bound i
renameTerm r (Lambda x t) = Lambda x (renameTerm r t)
renameTerm r (Con c ts) = Con c (map (renameTerm r) ts)
renameTerm r (Fun f) = Fun f
renameTerm r (Apply t ts) = Apply (renameTerm r t) (map (renameTerm r) ts)
renameTerm r (Case t bs) = Case (renameTerm r t) (map (\(c,xs,t) -> (c,xs,renameTerm r t)) bs)
renameTerm r (Let x t u) = Let x (renameTerm r t) (renameTerm r u)
renameTerm r (Letrec f xs t u) = Letrec f xs (renameTerm r t) (renameTerm r u)

-- redex

redex (Apply t u) = redex t
redex (Case t bs) = redex t
redex t = t


-- function name and args

fun (Apply t ts) = t

args (Apply t ts) = ts

-- unfold function

unfold (Apply t ts) fs d = let (t',d') = unfold t fs d
                           in  (Apply t' ts,d')
unfold (Case t bs) fs d = let (t',d') = unfold t fs d
                          in  (Case t' bs,d')
unfold (Fun f) fs d = case lookup f d of
                         Just (xs,t)-> (foldr (\x t->Lambda x (abstract t x)) t xs,d)
unfold (Let x t u) fs d = unfold (subst t u) fs d
unfold (Letrec f xs t u) fs d = let f' = rename fs f
                                    t' = concreteFun f' (foldr concrete t xs)
                                    u' = concreteFun f' u
                                in unfold u' (f':fs) ((f',(xs,t')):d)
unfold t fs d = (t,d)

-- pretty printing

stripLambda (Lambda x t) = let x' = rename (free t) x
                               (xs,u) = stripLambda $ concrete x' t
                           in  (x':xs,u)
stripLambda t = ([],t)

blank = P.space

prettyTerm (Free x) = text x
prettyTerm (Bound i) = text "#" <> int i
prettyTerm t@(Lambda _ _) = let (xs,t') = stripLambda t
                            in  text "\\" <> hsep (map text xs) <> text "." <> prettyTerm t'
prettyTerm t@(Con c ts)
   | isNat t   = int $ con2nat t
   | isList t  = text "[" <> hcat (punctuate comma $ map prettyTerm $ con2list t) <> text "]"
   | null ts   = text c
   | otherwise = text c <> parens (hcat $ punctuate comma $ map prettyTerm ts)
prettyTerm (Fun f) = text f
prettyTerm (Apply t ts ) = prettyAtom t <+> hsep (map prettyAtom ts)
prettyTerm (Case t (b:bs)) = hang (text "case" <+> prettyAtom t <+> text "of") 1 (blank <+> prettyBranch b $$ vcat (map ((text "|" <+>).prettyBranch) bs)) where
   prettyBranch (c,[],t) = text c <+> text "->" <+> prettyTerm t
   prettyBranch (c,xs,t) = let fv = foldr (\x fv -> let x' = rename fv x in x':fv) (free t) xs
                               xs' = take (length xs) fv
                               t' = foldr concrete t xs'
                           in  text c <> parens(hcat $ punctuate comma $ map text xs') <+> text "->" <+> prettyTerm t' $$ empty
prettyTerm (Let x t u) = let x' = rename (free u) x
                         in  (text "let" <+> text x' <+> text "=" <+> prettyTerm t) $$ (text "in" <+> prettyTerm (concrete x' u))
prettyTerm (Letrec f xs t u) = let fv = foldr (\x fv -> let x' = rename fv x in x':fv) (free t) xs
                                   f' = rename fv f
                                   xs' = take (length xs) fv
                                   t' = foldr concrete t (f':xs')
                                   u' = concrete f' u
                               in  (text "letrec" <+> text f' <+> hsep (map text xs') <+> text "=" <+> prettyTerm t') $$ (text "in" <+> prettyTerm u')

prettyAtom (Free x) = text x
prettyAtom t@(Con c ts)
   | isNat t   = int $ con2nat t
   | isList t  = text "[" <> hcat (punctuate comma $ map prettyTerm  $ con2list t) <> text "]"
   | null ts   = text c
   | otherwise = text c <> parens (hcat $ punctuate comma $ map prettyTerm ts)
prettyAtom (Fun f) = text f
prettyAtom t = parens $ prettyTerm t

prettyProg (t,d) = prettyProg' (("main",([],t)):d)

prettyProg' [] = empty
prettyProg' [(f,(xs,t))] = text f <+> hsep (map text xs) <+> equals <+> prettyTerm t
prettyProg' ((f,(xs,t)):fs) = text f <+> hsep (map text xs) <+> equals <+> prettyTerm t <> semi $$ prettyProg' fs

isList (Con "Nil" []) = True
isList (Con "Cons" [h,t]) = isList t
isList _ = False

list2con [] = Con "Nil" []
list2con (h:t) = Con "Cons" [h,list2con t]

con2list (Con "Nil" [])  = []
con2list (Con "Cons" [h,t]) = h:con2list t

isNat (Con "Zero" []) = True
isNat (Con "Succ" [n]) = isNat n
isNat _ = False

nat2con 0 = Con "Zero" []
nat2con n = Con "Succ" [nat2con $ n-1]

con2nat (Con "Zero" [])  = 0
con2nat (Con "Succ" [n]) = 1+con2nat n

-- lexing and parsing

potDef = emptyDef
         { commentStart    = "/*"
         , commentEnd      = "*/"
         , commentLine     = "--"
         , nestedComments  = True
         , identStart      = lower
         , identLetter     = letter <|> oneOf "_'"
         , reservedNames   = ["import", "case","of","let","in","letrec","ALL","EX","ANY"]
         , reservedOpNames = ["~","/\\","\\/","<=>","=>"]
         , caseSensitive   = True
         }

lexer = T.makeTokenParser potDef

symbol     = T.symbol lexer
bracks     = T.parens lexer
semic      = T.semi lexer
comm       = T.comma lexer
identifier = T.identifier lexer
reserved   = T.reserved lexer
reservedOp = T.reservedOp lexer
natural    = T.natural lexer

makeFuns ds = let fs = fst(unzip ds)
              in  map (\(f,(xs,t)) -> (f,(xs,makeFuns' fs t))) ds

makeFuns' fs (Free x) = if x `elem` fs then Fun x else Free x
makeFuns' fs (Bound i ) = Bound i
makeFuns' fs (Lambda x t) = Lambda x (makeFuns' fs t)
makeFuns' fs (Con c ts) = Con c (map (makeFuns' fs) ts)
makeFuns' fs (Apply t ts) = Apply (makeFuns' fs t) (map (makeFuns' fs) ts)
makeFuns' fs (Case t bs) = Case (makeFuns' fs t) (map (\(c,xs,t) -> (c,xs,makeFuns' fs t)) bs)
makeFuns' fs (Let x t u) = Let x (makeFuns' fs t) (makeFuns' fs u)
makeFuns' fs (Letrec f xs t u) = Letrec f xs (makeFuns' fs t) (makeFuns' fs u)

con = do
      c <- upper
      cs <- many letter
      spaces
      return (c:cs)

modul = do
        fs <- many imp
        ds <- sepBy1 fundef semic
        return (fs,ds)

imp = do
      reserved "import"
      con

expr =     do
           reserved "ALL"
           x <- identifier
           symbol ":"
           c <- con
           symbol "."
           e <- expr
           return (Apply (Free ("all"++c)) [Lambda x (abstract e x)])
       <|> do
           reserved "EX"
           x <- identifier
           symbol ":"
           c <- con
           symbol "."
           e <- expr
           return (Apply (Free ("ex"++c)) [Lambda x (abstract e x)])
       <|> do
           reserved "ANY"
           x <- identifier
           symbol ":"
           c <- con
           symbol "."
           e <- expr
           return (Apply (Free ("any"++c)) [Apply (Free "construct") [Lambda x (abstract e x)]])
       <|> term

fundef = do
         f <- identifier
         xs <- many identifier
         symbol "="
         e <- expr
         return (f,(xs,e))

term =     do
           t <- atom
           ts <- many atom
           return (makeApplication t ts)
       <|> do
           symbol "\\"
           xs <- many1 identifier
           symbol "->"
           t <- term
           return (foldr (\x t->Lambda x (abstract t x)) t xs)
       <|> do
           reserved "case"
           t <- term
           reserved "of"
           bs <- sepBy1 branch (symbol "|")
           return (Case t bs)
       <|> do
           reserved "let"
           x <- identifier
           symbol "="
           t <- term
           reserved "in"
           u <- term
           return (Let x t (abstract u x))
       <|> do
           reserved "letrec"
           f <- identifier
           xs <- many identifier
           symbol "="
           t <- term
           reserved "in"
           u <- term
           return (Letrec f xs (abstract (foldl abstract t xs) f) (abstract u f))

atom =     do
           x <- identifier
           return (Free x)
       <|> do
           c <- con
           ts <-     bracks (sepBy1 term comm)
                 <|> do
                     spaces
                     return []
           return (Con c ts)
       <|> do
           n <- natural
           return (nat2con n)
       <|> do
           symbol "["
           ts <- sepBy term comm
           symbol "]"
           return (list2con ts)
       <|> bracks expr

branch = do
         c <- con
         xs <-     bracks (sepBy1 identifier comm)
               <|> do
                   spaces
                   return []
         symbol "->"
         t <- term
         return (c,xs,foldl abstract t xs)

parseTerm = parse term "Parse error"

parseModule = parse modul "Parse error"



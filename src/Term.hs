module Term where

import Exception
import Prelude hiding ((<>))
import Data.Char
import Data.Maybe
import Data.List
import Data.Tuple
import Data.Foldable
import Control.Monad
import Text.PrettyPrint.HughesPJ as P
import Text.ParserCombinators.Parsec hiding (labels)
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
          | Apply Term Term -- application
          | Fun String -- function call
          | Case Term [(String,[String],Term)] -- case expression
          | Let String Term Term -- let expression
          | Unfold Term Term -- unfolding
          | Fold Term Term -- folding

instance Show Term where
   show t = render $ prettyTerm t

type Prog = (Term,[(String,([String],Term))])

showProg p = render $ prettyProg p

-- equality of terms

instance Eq Term where
   (==) t t' = eqTerm (t,t')

eqTerm (Free x,Free x') = x==x'
eqTerm (Bound i,Bound i') = i==i'
eqTerm (Lambda x t,Lambda x' t') = eqTerm (t,t')
eqTerm (Con c ts,Con c' ts') | c==c' = all eqTerm (zip ts ts')
eqTerm (Apply t u,Apply t' u') = eqTerm (t,t') && eqTerm (u,u')
eqTerm (Fun f,Fun f') = f==f'
eqTerm (Case t bs,Case t' bs') | matchCase bs bs' = eqTerm (t,t') && all (\((_,_,t),(_,_,t')) -> eqTerm (t,t')) (zip bs bs')
eqTerm (Let x t u,Let x' t' u') = eqTerm (t,t') && eqTerm (u,u')
eqTerm (Unfold t u,Unfold t' u') = eqTerm (t,t') && eqTerm (u,u')
eqTerm (Fold t u,Fold t' u') = eqTerm (t,t') && eqTerm (u,u')
eqTerm (t,t') = False

-- context surrounding redex

data Context = EmptyCtx
             | ApplyCtx Context Term
             | CaseCtx Context [(String,[String],Term)] deriving Show

-- place term in context

place t EmptyCtx = t
place t (ApplyCtx con u) = place (Apply t u) con
place t (CaseCtx con bs) = place (Case t bs) con

redex (Apply t u) = redex t
redex (Case t bs) = redex t
redex t = t

matchRedex (Fun f) (Fun f') = f==f'
matchRedex (Unfold t u) (Unfold t' u') = True
matchRedex t u = False

matchCase bs bs' = length bs == length bs' && all (\((c,xs,t),(c',xs',t')) -> c == c' && length xs == length xs') (zip bs bs')

-- term instance

inst t t' = inst' t t' (free t++free t') [] []

inst' (Free x) t fv bv s | x `elem` bv = [s | t==Free x]
inst' (Free x) t fv bv s = if   x `elem` map fst s
                           then [s | (x,t) `elem` s]
                           else [(x,t):s]
inst' (Bound i) (Bound i') fv bv s | i==i' = [s]
inst' (Lambda x t) (Lambda x' t') fv bv s = let x'' = renameVar (fv++bv) x
                                            in  inst' (concrete x'' t) (concrete x'' t') fv (x'':bv) s
inst' (Con c ts) (Con c' ts') fv bv s | c==c' = foldr (\(t,t') ss -> concat [inst' t t' fv bv s | s <- ss]) [s] (zip ts ts')
inst' (Apply t (Free x)) u fv bv s | x `elem` bv = inst' t (Lambda x (abstract u x)) fv bv s
inst' (Apply t u) (Apply t' u') fv bv s = concat [inst' u u' fv bv s' | s' <- inst' t t' fv bv s]
inst' (Fun f) (Fun f') fv bv s | f==f' = [s]
inst' (Case t bs) (Case t' bs') fv bv s | matchCase bs bs' = foldr (\((c,xs,t),(c',xs',t')) ss -> let fv' = renameVars (fv++bv) xs
                                                                                                      xs'' = take (length xs) fv'
                                                                                                  in  concat [inst' (foldr concrete t xs'') (foldr concrete t' xs'') fv (xs''++bv) s | s <- ss]) (inst' t t' fv bv s) (zip bs bs')
inst' (Let x t u) (Let x' t' u') fv bv s = let x'' = renameVar (fv++bv) x
                                           in concat [inst' (concrete x'' u) (concrete x'' u') fv (x'':bv) s' | s' <- inst' t t' fv bv s]
inst' (Unfold t u) (Unfold t' u') fv bv s = inst'  u u' fv bv s
inst' (Fold t u) (Fold t' u') fv bv s | t==t' = [s] 
inst' t t' fv bv s = []

instTerm t t' = not (null (inst t t'))

instLTS (t,s) (t',s') = instTerm (instantiate s t) (instantiate s' t')

-- homeomorphic embedding

embedding t u = couple t u []

embed t u r = couple t u r ++ dive t u r 

couple (Free x) (Free x') r = if x `elem` map snd r then [r | (x',x) `elem` r] else [(x',x):r]
couple (Bound i) (Bound i') r | i == i' = [r]
couple (Lambda x t) (Lambda x' t') r = embed t t' r
couple (Con c ts) (Con c' ts') r | c==c' = foldr (\(t,t') rs -> concat [embed t t' r | r <- rs]) [r] (zip ts ts')
couple (Apply t u) (Apply t' u') r = concat [embed u u' r' | r' <- embed t t' r]
couple (Fun f) (Fun f') r | f==f' = [r]
couple (Case t bs) (Case t' bs') r | matchCase bs bs' = foldr (\((c,xs,t),(c',xs',t')) rs -> concat [embed t t' r | r <- rs]) (embed t t' r) (zip bs bs')
couple (Let x t u) (Let x' t' u') r = concat [embed u u' r' | r' <- embed t t' r]
couple (Unfold t u) (Unfold t' u') r = embed  u u' r
couple (Fold t u) (Fold t' u') r | t==t' = [r]
couple t t' r = []

dive t (Lambda x t') r = embed t (concrete x t') r
dive t (Con c ts) r = concat [embed t t' r | t' <- ts]
dive t (Apply t' u) r = embed t t' r ++ embed t u r
dive t (Case t' bs) r = embed t t' r ++ concatMap (\(c,xs,t') -> embed t (foldr concrete t' xs) r) bs
dive t (Let x t' u) r = embed t t' r ++ embed t u r
dive t (Unfold _ u) r = embed t (concrete "f" u) r
dive t t' r = []

embedTerm t t' = not (null (embedding t t')) && matchRedex (redex t) (redex t')

embedLTS (t,s) (t',s') = embedTerm (instantiate s t) (instantiate s' t')

-- generalisation

generalise t u = generalise' t u (free t++free u) [] [] []

generalise' (Free x) (Free x') fv bv s1 s2 | x==x' = (Free x,s1,s2)
generalise' (Free x) t fv bv s1 s2 | x `elem` bv = (Free x,(x,Free x):s1,(x,t):s2)
generalise' (Bound i) (Bound i') fv bv s1 s2 | i==i' = (Bound i,s1,s2)
generalise' (Lambda x t) (Lambda x' t') fv bv s1 s2 = let x'' = renameVar (fv++map fst s1) x
                                                          (t'',s1',s2') = generalise' (concrete x'' t) (concrete x'' t') (x'':fv) (x'':bv) s1 s2
                                                      in  (Lambda x (abstract t'' x''),s1',s2')
generalise' (Con c ts) (Con c' ts') fv bv s1 s2 | c==c' = let ((s1',s2'),ts'') = mapAccumL (\(s1,s2) (t,t') -> let (t'',s1',s2') = generalise' t t' fv bv s1 s2
                                                                                                               in  ((s1',s2'),t'')) (s1,s2) (zip ts ts')
                                                          in  (Con c ts'',s1',s2')
generalise' (Apply t u) (Apply t' u') fv bv s1 s2 = let (t'',s1',s2') = generalise' t t' fv bv s1 s2
                                                        (u'',s1'',s2'') = generalise' u u' fv bv s1' s2'         
                                                    in  (Apply t'' u'',s1'',s2'')
generalise' (Fun f) (Fun f') fv bv s1 s2 | f==f' = (Fun f,s1,s2)
generalise' (Case t bs) (Case t' bs') fv bv s1 s2 | matchCase bs bs' = let (t'',s1',s2') = generalise' t t' fv bv s1 s2
                                                                           ((s1'',s2''),bs'') = mapAccumL (\(s1,s2) ((c,xs,t),(c',xs',t')) -> let fv' = renameVars (fv++map fst s1) xs
                                                                                                                                                  xs' = take (length xs) fv'
                                                                                                                                                  (t'',s1',s2') = generalise' t t' (xs'++fv) (xs'++bv) s1 s2
                                                                                                                                              in ((s1',s2'),(c,xs,t''))) (s1',s2') (zip bs bs')
                                                                       in  (Case t'' bs'',s1'',s2'')
generalise' (Let x t u) (Let x' t' u') fv bv s1 s2 = let x'' = renameVar (fv++map fst s1) x
                                                         (t'',s1',s2') = generalise' t t' fv bv s1 s2
                                                         (u'',s1'',s2'') = generalise' (concrete x'' u) (concrete x'' u') (x'':fv) (x'':bv) s1' s2'
                                                     in  (Let x t'' (abstract u'' x''),s1'',s2'')
generalise' (Unfold t u) (Unfold t' u') fv bv s1 s2 = let xs = free t
                                                          (u'',s1',s2') = generalise' u u' (xs++fv) (xs++bv) s1 s2
                                                      in  (Unfold t u'',s1',s2')
generalise' (Fold t u) (Fold t' u') fv bv s1 s2 | t==t' = (Fold t u,s1,s2)
generalise' t u fv bv s1 s2 = let xs = intersect bv (free t)
                                  t' = foldl (\t x -> Lambda x (abstract t x)) t xs    
                                  u' = foldl (\t x -> Lambda x (abstract t x)) u xs 
                              in  case find (\(x,t) -> t==t' && (lookup x s2 == Just u')) s1 of
                                     Just (x,t) -> (foldr (\x t -> Apply t (Free x)) (Free x) xs,s1,s2)
                                     Nothing -> let x = renameVar (fv++map fst s1) "x"
                                                in  (foldr (\x t -> Apply t (Free x)) (Free x) xs,(x,t'):s1,(x,u'):s2)

-- Program residualisation

residualise (t,d) = residualise' t (free t) [] d

residualise' (Free x) fv m d = (Free x,d)
residualise' (Bound i) fv m d = (Bound i,d)
residualise' (Lambda x t) fv m d = let x' = renameVar fv x
                                       (t',d') = residualise' (concrete x' t) (x':fv) m d
                                   in  (Lambda x (abstract t' x'),d')
residualise' (Con c ts) fv m d = let (d',ts') = mapAccumL (\d t -> let (t',d') = residualise' t fv m d
                                                                   in  (d',t')) d ts
                                 in  (Con c ts',d')
residualise' (Apply t u) fv m d = let (t',d') = residualise' t fv m d
                                      (u',d'') = residualise' u fv m d'
                                  in  (Apply t' u',d'')
residualise' (Fun f) fv m d = (Fun f,d)
residualise' (Case t bs) fv m d = let (t',d') = residualise' t fv m d
                                      (d'',bs') = mapAccumL (\d (c,xs,t) -> let fv' = renameVars fv xs
                                                                                xs' = take (length xs) fv'
                                                                                (t',d') = residualise' (foldr concrete t xs') fv' m d
                                                                            in  (d',(c,xs,foldl abstract t' xs'))) d' bs
                                  in  (Case t' bs',d'')
residualise' (Let x t u) fv m d = let x' = renameVar fv x
                                      (t',d') = residualise' t fv m d
                                      (u',d'') = residualise' (concrete x' u) (x':fv) m d'
                                  in  (Let x t' (abstract u' x'),d'')
residualise' (Unfold t u) fv m d = let f = renameVar (map fst d ++ map fst m) "f"
                                       xs = free u
                                       (t',d') = residualise' (concrete f u) fv ((f,(xs,t)):m) d
                                   in  (foldl (\t x -> Apply t (Free x)) (Fun f) xs,(f,(xs,foldl abstract t' xs)):d')
residualise' (Fold (Free f) t) fv m d = case lookup f m of
                                           Just (xs,t') -> let s = head (inst t' t)
                                                               (d',s') = mapAccumL (\d (x,t) -> let (t',d') = residualise' t fv m d
                                                                                                in  (d',(x,t'))) d s
                                                           in  (instantiate s' (foldl (\t x -> Apply t (Free x)) (Fun f) xs),d')
                                           Nothing -> residualise' t fv m d                                                            

makeLet s t = foldl (\u (x,t) -> Let x t (abstract u x)) t s

eval (Free x) k d r a = error ("Unbound identifier: "++x)
eval (Lambda x t) EmptyCtx d r a = (Lambda x t,r,a)
eval (Lambda x t) (ApplyCtx k u) d r a = eval (subst u t) k d (r+1) a
eval (Lambda x t) (CaseCtx k bs) d r a = error ("Unapplied function in case selector: " ++ show (Lambda x t))
eval (Con c ts) EmptyCtx d r a = let ((r',a'),ts') = mapAccumL (\(r,a) t -> let (t',r',a') = eval t EmptyCtx d r a
                                                                            in  ((r',a'),t')) (r,a) ts
                                 in  (Con c ts',r'+1,a')
eval (Con c ts) (ApplyCtx k u) d r a = error ("Constructor application is not saturated: "++show (place (Con c ts) (ApplyCtx k u)))
eval (Con c ts) (CaseCtx k bs) d r a = case find (\(c',xs,t) -> c==c' && length xs == length ts) bs of
                                          Nothing -> error ("No matching pattern in case for term:\n\n"++show (Case (Con c ts) bs))
                                          Just (c',xs,t) -> eval (foldr subst t ts) k d (r+length ts) (a+1)
eval (Apply t u) k d r a = eval t (ApplyCtx k u) d r a
eval (Fun f) k d r a = case lookup f d of
                          Nothing -> error ("Undefined function: "++f)
                          Just (xs,t)  -> eval (foldr Lambda t xs) k d (r+1) a
eval (Case t bs) k d r a = eval t (CaseCtx k bs) d r a
eval (Let x t u) k d r a = eval (subst t u) k d (r+1) a

-- free variables in a term

free t = nub (free' t)

free' (Free x) = [x]
free' (Bound i) = []
free' (Lambda x t) = free' t
free' (Con c ts) = concatMap free' ts
free' (Apply t u)  = free' t ++ free' u
free' (Fun f) = []
free' (Case t bs) = free' t ++ concatMap (\(c,xs,t) -> free' t) bs
free' (Let x t u) = free' t  ++ free' u
free' (Unfold t u) = free' u
free' (Fold t u) = free' t ++ free' u

-- funs in a prog

funs (t,d) = funs' d t []

funs' d (Free x) fs = fs
funs' d (Bound i) fs = fs
funs' d (Lambda x t) fs = funs' d t fs
funs' d (Con c ts) fs = foldr (funs' d) fs ts
funs' d (Apply t u) fs = funs' d t (funs' d u fs)
funs' d (Fun f) fs = if   f `elem` fs
                     then fs
                     else case lookup f d of
                             Nothing -> f:fs
                             Just (xs,t)  -> funs' d t (f:fs)
funs' d (Case t bs) fs = foldr (\(_,_,t) fs -> funs' d t fs) (funs' d t fs) bs
funs' d (Let x t u) fs = funs' d t (funs' d u fs)

-- shift global de Bruijn indices by i, where current depth is d

shift = shift' 0

shift' d 0 u = u
shift' d i (Free x) = Free x
shift' d i (Bound i') = if i' >= d then Bound (i'+i) else Bound i'
shift' d i (Lambda x t) = Lambda x (shift' (d+1) i t)
shift' d i (Con c ts) = Con c (map (shift' d i) ts)
shift' d i (Apply t u) = Apply (shift' d i t) (shift' d i u)
shift' d i (Fun f) = Fun f
shift' d i (Case t bs) = Case (shift' d i t) (map (\(c,xs,t) -> (c,xs,shift' (d+length xs) i t)) bs)
shift' d i (Let x t u) = Let x (shift' d i t) (shift' (d+1) i u)
shift' d i (Unfold t u) = Unfold (shift' d i t) (shift' (d+1) i u)
shift' d i (Fold t u) = Fold (shift' d i t) (shift' d i u)

-- substitute term t for variable with de Bruijn index i

subst = subst' 0

subst' i t (Free x) = Free x
subst' i t (Bound i')
   | i'<i      = Bound i'
   | i'==i     = shift i t
   | otherwise = Bound (i'-1)
subst' i t (Lambda x t') = Lambda x (subst' (i+1) t t')
subst' i t (Con c ts) = Con c (map (subst' i t) ts)
subst' i t (Apply t' u) = Apply (subst' i t t') (subst' i t u)
subst' i t (Fun f) = Fun f
subst' i t (Case t' bs) = Case (subst' i t t') (map (\(c,xs,u) -> (c,xs,subst' (i+length xs) t u)) bs)
subst' i t (Let x t' u) = Let x (subst' i t t') (subst' (i+1) t u)
subst' i t (Unfold t' u) = Unfold (subst' i t t') (subst' (i+1) t u)
subst' i t (Fold t' u) = Fold (subst' i t t') (subst' i t u)

-- rename a term t using renaming r

rename r (Free x) = case lookup x r of
                       Just x'  -> Free x'
                       Nothing -> Free x
rename r (Bound i) = Bound i
rename r (Lambda x t) = Lambda x (rename r t)
rename r (Con c ts) = Con c (map (rename r) ts)
rename r (Apply t u) = Apply (rename r t) (rename r u)
rename r (Fun f) = Fun f
rename r (Case t bs) = Case (rename r t) (map (\(c,xs,t) -> (c,xs,rename r t)) bs)
rename r (Let x t u) = Let x (rename r t) (rename r u)
rename r (Unfold t u) = Unfold (rename r t) (rename r u)
rename r (Fold t u) = Fold (rename r t) (rename r u)

-- instantiate a term t using substitution s

instantiate = instantiate' 0

instantiate' d s (Free x) = case lookup x s of
                               Just t  -> shift d t
                               Nothing -> Free x
instantiate' d s (Bound i) = Bound i
instantiate' d s (Lambda x t) = Lambda x (instantiate' (d+1) s t)
instantiate' d s (Con c ts) = Con c (map (instantiate' d s) ts)
instantiate' d s (Apply t u) = Apply (instantiate' d s t) (instantiate' d s u)
instantiate' d s (Fun f) = Fun f
instantiate' d s (Case t bs) = Case (instantiate' d s t) (map (\(c,xs,t) -> (c,xs,instantiate' (d+length xs) s t)) bs)
instantiate' d s (Let x t u) = Let x (instantiate' d s t) (instantiate' (d+1) s u)
instantiate' d s (Unfold t u) = Unfold (instantiate' d s t) (instantiate' (d+1) s u)
instantiate' d s (Fold t u) = Fold (instantiate' d s t) (instantiate' d s u)

-- replace variable x with de Bruijn index

abstract = abstract' 0

abstract' i (Free x') x = if x==x' then Bound i else Free x'
abstract' i (Bound i') x = if i'>=i then Bound (i'+1) else Bound i'
abstract' i (Lambda x' t) x = Lambda x' (abstract' (i+1) t x)
abstract' i (Con c ts) x = Con c (map (\t -> abstract' i t x) ts)
abstract' i (Apply t u) x = Apply (abstract' i t x) (abstract' i u x)
abstract' i (Fun f) x = Fun f
abstract' i (Case t bs) x = Case (abstract' i t x) (map (\(c,xs,t) -> (c,xs,abstract' (i+length xs) t x)) bs)
abstract' i (Let x' t u) x = Let x' (abstract' i t x) (abstract' (i+1) u x)
abstract' i (Unfold t u) x = Unfold (abstract' i t x) (abstract' (i+1) u x)
abstract' i (Fold t u) x = Fold (abstract' i t x) (abstract' i u x)

-- replace de Bruijn index 0 with variable x

concrete = concrete' 0

concrete' i x (Free x') = Free x'
concrete' i x (Bound i')
   | i'<i = Bound i'
   | i'==i = Free x
   | otherwise = Bound (i'-1)
concrete' i x (Lambda x' t) = Lambda x' (concrete' (i+1) x t)
concrete' i x (Con c ts) = Con c (map (concrete' i x) ts)
concrete' i x (Apply t u) = Apply (concrete' i x t) (concrete' i x u)
concrete' i x (Fun f) = Fun f
concrete' i x (Case t bs) = Case (concrete' i x t) (map (\(c,xs,t) -> (c,xs,concrete' (i+length xs) x t)) bs)
concrete' i x (Let x' t u) = Let x' (concrete' i x t) (concrete' (i+1) x u)
concrete' i x (Unfold t u) = Unfold (concrete' i x t) (concrete' (i+1) x u)
concrete' i x (Fold t u) = Fold (concrete' i x t) (concrete' i x u)

-- rename variable x so it does not clash with any of fv

renameVar fv x = if   x `elem` fv
                 then renameVar fv (x++"'")
                 else x

renameVars = foldr (\x fv -> let x' = renameVar fv x in x':fv)

-- unfold function

unfold (Apply t u,d) = let t' = unfold (t,d)
                        in  Apply t' u
unfold (Case t bs,d) = let t' = unfold (t,d)
                       in  Case t' bs
unfold (Fun f,d) = case lookup f d of
                    Nothing -> error ("Undefined function: "++f)
                    Just (xs,t) -> foldr Lambda t xs
unfold (t,d) = t

args (Apply t u) = args t ++ [u]
args _ = []

-- pretty printing

stripLambda (Lambda x t) = let x' = renameVar (free t) x
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
prettyTerm (Apply t u) = prettyTerm t <+> prettyAtom u
prettyTerm (Fun f) = text f
prettyTerm (Case t (b:bs)) = hang (text "case" <+> prettyAtom t <+> text "of") 1 (blank <+> prettyBranch b $$ vcat (map ((text "|" <+>).prettyBranch) bs)) where
   prettyBranch (c,[],t) = text c <+> text "->" <+> prettyTerm t
   prettyBranch (c,xs,t) = let fv = renameVars (free t) xs
                               xs' = take (length xs) fv
                               t' = foldr concrete t xs'
                           in  text c <> parens(hcat $ punctuate comma $ map text xs') <+> text "->" <+> prettyTerm t' $$ empty
prettyTerm (Let x t u) = let x' = renameVar (free u) x
                         in  (text "let" <+> text x' <+> text "=" <+> prettyTerm t) $$ (text "in" <+> prettyTerm (concrete x' u))
prettyTerm (Unfold t u) = text "Unfold" <+> prettyAtom t <+> text "=" <+> prettyTerm u
prettyTerm (Fold t u) = text "Fold" <+> prettyAtom t <+> prettyAtom u

prettyAtom (Free x) = text x
prettyAtom t@(Con c ts)
   | isNat t   = int $ con2nat t
   | isList t  = text "[" <> hcat (punctuate comma $ map prettyTerm  $ con2list t) <> text "]"
   | null ts   = text c
   | otherwise = text c <> parens (hcat $ punctuate comma $ map prettyTerm ts)
prettyAtom (Fun f) = text f
prettyAtom t = parens $ prettyTerm t

prettyProg (t,d) = let d' = [f | f <- d, fst f `elem` funs (t,d)]          
                   in  prettyEnv (("main",([],t)):d')

prettyEnv [] = empty
prettyEnv [(f,(xs,t))] = text f <+> hsep (map text xs) <+> equals <+> prettyTerm (foldr concrete t xs)
prettyEnv ((f,(xs,t)):fs) = text f <+> hsep (map text xs) <+> equals <+> prettyTerm (foldr concrete t xs) <> semi $$ prettyEnv fs

isList (Con "Nil" []) = True
isList (Con "Cons" [h,t]) = isList t
isList _ = False

list2con [] = Con "Nil" []
list2con (h:t) = Con "Cons" [h,list2con t]

con2list (Con "Nil" [])  = []
con2list (Con "Cons" [h,t]) = h:con2list t

range2con m n = if    m > n 
                then Con "Nil" []
                else Con "Cons" [nat2con m,range2con (m+1) n]

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
         , identLetter     = letter <|> digit <|> oneOf "_'"
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

con = do
      c <- upper
      cs <- many letter
      spaces
      return (c:cs)

makeProg ds = let fs = map fst ds
                  ds' =  map (\(f,(xs,t)) -> (f,(xs,foldl abstract (makeFun fs t) xs))) ds
              in  case lookup "main" ds' of
                     Nothing -> error "No main function"
                     Just (xs,t) -> (t,delete ("main",(xs,t)) ds')

makeFun fs (Free x) = if x `elem` fs then Fun x else Free x
makeFun fs (Bound i) = Bound i
makeFun fs (Lambda x t) = Lambda x (makeFun fs t)
makeFun fs (Con c ts) = Con c (map (makeFun fs) ts)
makeFun fs (Apply t u) = Apply (makeFun fs t) (makeFun fs u)
makeFun fs (Fun f) = Fun f
makeFun fs (Case t bs) = Case (makeFun fs t) (map (\(c,xs,t) -> (c,xs,makeFun fs t)) bs)
makeFun fs (Let x t u) = Let x (makeFun fs t) (makeFun fs u)

modul = do
        fs <- many imp
        ds <- sepBy1 fundef semic
        return (fs,ds)

imp = do
      reserved "import"
      con

fundef = do
         f <- identifier
         xs <- many identifier
         symbol "="
         e <- term
         return (f,(xs,e))

term =     do
           a <- atom
           as <- many atom
           return (foldl Apply a as)
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

atom =     do Free <$> identifier
       <|> do
           c <- con
           ts <- option [] (bracks (sepBy1 term comm))
           return (Con c ts) 
       <|> do 
           m <- natural
           option (nat2con m) (do symbol ".." 
                                  range2con m <$> natural)
       <|> do
           symbol "["
           ts <- sepBy term comm
           symbol "]"
           return (list2con ts)
       <|> bracks term

branch = do
         c <- con
         xs <- option [] (bracks (sepBy1 identifier comm))
         symbol "->"
         t <- term
         return (c,xs,foldl abstract t xs)

parseTerm = parse term "Parse error"

parseModule = parse modul "Parse error"



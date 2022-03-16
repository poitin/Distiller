module Tree where

import Term
import Prelude hiding ((<>))
import Data.Char
import Data.Maybe
import Data.List
import Data.Tuple
import Data.Foldable
import Data.Bifunctor
import Control.Monad
import Text.PrettyPrint.HughesPJ as P
import Text.ParserCombinators.Parsec hiding (labels)
import Text.ParserCombinators.Parsec.Expr
import qualified Text.ParserCombinators.Parsec.Token as T
import Text.ParserCombinators.Parsec.Language
import System.IO
import System.Directory

-- process trees

data Tree = Var String -- variable
          | Abs String Tree -- lambda abstraction
          | Cons String [Tree] -- constructor
          | App Tree Tree -- application
          | Choice Tree [(String,[String],Tree)] -- case
          | Gen String Tree Tree -- generalisation node 
          | Unfold String Tree -- unfold node
          | Fold String [(String,Tree)] -- fold node

matchChoice bs bs' = length bs == length bs' && all (\((c,xs,t),(c',xs',t')) -> c == c' && length xs == length xs') (zip bs bs')

-- equality of process trees

instance Eq Tree where
   (==) t t' = eqTree [] t t' [] 

eqTree fs (Var x) (Var x') r | x `elem` map fst r = (x,x') `elem` r
eqTree fs (Var x) (Var x') r  = x==x'
eqTree fs (Abs x t) (Abs x' t') r  = eqTree fs t t' ((x,x'):r)
eqTree fs (Cons c ts) (Cons c' ts') r | c==c' = all (\(t,t') -> eqTree fs t t' r) (zip ts ts')
eqTree fs (App t u) (App t' u') r = eqTree fs t t' r && eqTree fs u u' r 
eqTree fs (Choice t bs) (Choice t' bs') r | matchChoice bs bs' = eqTree fs t t' r && all (\((c,xs,t),(c',xs',t')) -> eqTree fs t t' (zip xs xs'++r)) (zip bs bs')
eqTree fs (Gen x t u) (Gen x' t' u') r = eqTree fs t t' r && eqTree fs u u' ((x,x'):r)
eqTree fs (Unfold f t) (Unfold f' t') r = eqTree ((f,f'):fs) t t' r 
eqTree fs (Fold f _) (Fold f' _) r = (f,f') `elem` fs 
eqTree fs t t' r = False

-- process tree renaming

renamingTree t t' = renamingTree' [] t t' []

renamingTree' fs (Var x) (Var x') r = if   x `elem` map fst r || x' `elem` map snd r
                                      then [r | (x,x') `elem` r] 
                                      else [(x,x'):r]
renamingTree' fs (Abs x t) (Abs x' t') r = renamingTree' fs t t' ((x,x'):r)
renamingTree' fs (Cons c ts) (Cons c' ts') r | c==c' = foldr (\(t,t') rs -> concat [renamingTree' fs t t' r | r <- rs]) [r] (zip ts ts')
renamingTree' fs (App t u) (App t' u') r = concat [renamingTree' fs u u' r' | r' <- renamingTree' fs t t' r]
renamingTree' fs (Choice t bs) (Choice t' bs') r = foldr (\((c,xs,t),(c',xs',t')) rs -> concat [renamingTree' fs t t' (zip xs xs' ++ r) | r <- rs]) (renamingTree' fs t t' r) (zip bs bs') 
renamingTree' fs (Gen x t u) (Gen x' t' u') r = concat [renamingTree' fs u u' ((x,x'):r') | r' <- renamingTree' fs t t' r]
renamingTree' fs (Unfold f u) (Unfold f' u') r = renamingTree' ((f,f'):fs) u u' r
renamingTree' fs (Fold f s) (Fold f' s') r | (f,f') `elem` fs = foldr (\((x,t),(x',t')) rs -> concat [renamingTree' fs t t' r' | r' <- renamingTree' fs (Var x) (Var x') r]) [r] (zip s s')
renamingTree' fs t t' r = []

-- process tree instance 

instTree t u = instTree' [] t u [] []

instTree' fs (Var x) (Var x') r s | x `elem` map fst r = [s | (x,x') `elem` r] 
instTree' fs (Var x) t r s | x `elem` map fst r = []
instTree' fs (Var x) t r s = if   x `elem` map fst s
                             then [s | (x,t) `elem` s]
                             else [(x,t):s]
instTree' fs (Abs x t) (Abs x' t') r s = instTree' fs t t' ((x,x'):r) s
instTree' fs (Cons c ts) (Cons c' ts') r s | c==c' = foldr (\(t,t') ss -> concat [instTree' fs t t' r s | s <- ss]) [s] (zip ts ts')
instTree' fs (App t u) (App t' u') r s = concat [instTree' fs u u' r s' | s' <- instTree' fs t t' r s]
instTree' fs (Choice t bs) (Choice t' bs') r s | matchChoice bs bs' = foldr (\((c,xs,t),(c',xs',t')) ss -> concat [instTree' fs t t' (zip xs xs' ++ r) s | s <- ss]) (instTree' fs t t' r s) (zip bs bs')  
instTree' fs (Gen x t u) (Gen x' t' u') r s = concat [instTree' fs u u' ((x,x'):r) s' | s' <- instTree' fs t t' r s]
instTree' fs (Unfold f t) (Unfold f' t') r s = instTree' ((f,f'):fs) t t' r s
instTree' fs (Fold f _) (Fold f' _) r s = [s | (f,f') `elem` fs]
instTree' fs t t' r s = []

-- homeomorphic embedding of process trees

embeddingTree = coupleTree []

embedTree fs t u = coupleTree fs t u || diveTree fs t u
 
coupleTree fs (Var x) (Var x') = True
coupleTree fs (Abs x t) (Abs x' t') = embedTree fs t t' 
coupleTree fs (Cons c ts) (Cons c' ts') | c==c' = all (uncurry (embedTree fs)) (zip ts ts')
coupleTree fs (App t u) (App t' u') = embedTree fs u u' && embedTree fs t t'
coupleTree fs (Choice t bs) (Choice t' bs') | matchChoice bs bs' = embedTree fs t t' && all (\((c,xs,t),(c',xs',t'))-> embedTree fs t t') (zip bs bs') 
coupleTree fs (Gen x t u) (Gen x' t' u') = embedTree fs t t' && embedTree fs u u'
coupleTree fs (Unfold f t) (Unfold f' t') = embedTree ((f,f'):fs) t t'
coupleTree fs (Fold f _) (Fold f' _) = (f,f') `elem` fs
coupleTree fs t t' = False

diveTree fs t (Abs x t') = embedTree fs t t'
diveTree fs t (Cons c ts) = any (embedTree fs t) ts
diveTree fs t (App t' u) = embedTree fs t t' || embedTree fs t u
diveTree fs t (Choice t' bs) = embedTree fs t t' || any (\(c,xs,t') -> embedTree fs t t') bs
diveTree fs t (Gen x t' u) = embedTree fs t t' || embedTree fs t u
diveTree fs t (Unfold t' u) = embedTree fs t u
diveTree fs t t' = False

-- generalisation of process trees 

generaliseTree t t' = generaliseTree' [] t t' (varsTree t) [] []

generaliseTree' fs (Var x) (Var x') fv s1 s2 = (Var x,s1,s2)
generaliseTree' fs (Var x) t fv s1 s2 | x `elem` freeTree t = (Var x,s1,(x,t):s2)
generaliseTree' fs (Abs x t) (Abs x' t') fv s1 s2 = let (t'',s1',s2') = generaliseTree' fs t t' fv s1 s2
                                                    in  (Abs x t'',s1',s2')
generaliseTree' fs (Cons c ts) (Cons c' ts') fv s1 s2 | c==c' = let ((s1',s2'),ts'') = mapAccumL (\(s1,s2) (t,t') -> let (t'',s1',s2') = generaliseTree' fs t t' fv s1 s2
                                                                                                                     in  ((s1',s2'),t'')) (s1,s2) (zip ts ts')
                                                                in  (Cons c ts'',s1',s2')
generaliseTree' fs (App t u) (App t' u') fv s1 s2 = let (t'',s1',s2') = generaliseTree' fs t t' fv s1 s2
                                                        (u'',s1'',s2'') = generaliseTree' fs u u' fv s1' s2'
                                                    in  (App t'' u'',s1'',s2'')
generaliseTree' fs (Choice t bs) (Choice t' bs') fv s1 s2 | matchChoice bs bs' = let (t'',s1',s2') = generaliseTree' fs t t' fv s1 s2
                                                                                     ((s1'',s2''),bs'') = mapAccumL (\(s1,s2) ((c,xs,t),(c',xs',t')) -> let (t'',s1',s2') = generaliseTree' fs t t' fv s1 s2
                                                                                                                                                        in  ((s1',s2'),(c,xs,t''))) (s1',s2') (zip bs bs')                                                     
                                                                                 in  (Choice t'' bs'',s1'',s2'')
generaliseTree' fs (Gen x t u) (Gen x' t' u') fv s1 s2 = let (u'',s1',s2') = generaliseTree' fs u (renameTree [(x',x)] u') fv s1 s2
                                                         in  if   x `elem` map fst s2'
                                                             then let x' = renameVar (fv++map fst s1') "x"
                                                                  in  (Gen x (Var x') u'',(x',t):s1',s2')
                                                               else (Gen x t u'',s1',s2')
generaliseTree' fs (Unfold f t) (Unfold f' t') fv s1 s2 = let (t'',s1',s2') = generaliseTree' ((f,f'):fs) t t' fv s1 s2
                                                          in  (Unfold f t'',s1',s2')
generaliseTree' fs (Fold f s) (Fold f' s') fv s1 s2 | (f,f') `elem` fs = (Fold f s,s1,s2)
generaliseTree' fs t u fv s1 s2 = case [x | (x,t') <- s1, (x',u') <- s2, x==x' && t==t' && u==u'] of
                                     (x:_) -> (Var x,s1,s2)
                                     [] -> let x = renameVar (fv++map fst s1) "x"
                                           in  (Var x,(x,t):s1,(x,u):s2)

makeGen s t = foldl (\u (x,t) -> Gen x t u) t s

-- Final program residualisation

residualise t s = let (t',s',d) = residualise' t (freeTree t) [] [] s []
                  in  (t',s',[(f,(xs,t')) | (f,(xs,t,t')) <- d])
 
residualise' (Var x) fv bv m s d | x `elem` map fst s = let Just t = lookup x s
                                                            (t',s',d') = residualise' t fv bv m s d
                                                            xs = free t' `intersect` bv
                                                        in  (foldl (\t x -> Apply t (Free x)) (Free x) xs,(x,foldr (\x t->Lambda x (abstract t x)) t' xs):s',d')
residualise' (Var x) fv bv m s d = (Free x,[],d)
residualise' (Abs x t) fv bv m s d = let (t',s',d') = residualise' t fv (x:bv) m s d
                                     in  (Lambda x (abstract t' x),s',d')
residualise' (Cons c ts) fv bv m s d = let ((s',d'),ts') = mapAccumL (\(s',d) t -> let (t',s'',d') = residualise' t fv bv m s d
                                                                                   in  ((s'++s'',d'),t')) ([],d) ts
                                       in  (Con c ts',s',d')
residualise' (App t u) fv bv m s d = let (t',s',d') = residualise' t fv bv m s d
                                         (u',s'',d'') = residualise' u fv bv m s d'
                                     in  (Apply t' u',s'++s'',d'')
residualise' (Choice t bs) fv bv m s d = let (t',s',d') = residualise' t fv bv m s d
                                             ((s'',d''),bs') = mapAccumL (\(s',d) (c,xs,t) -> let (t',s'',d') = residualise' t fv (xs++bv) m s d
                                                                                              in  ((s'++s'',d'),(c,xs,foldl abstract t' xs))) (s',d') bs
                                         in  (Case t' bs',s'++s'',d'')
residualise' (Gen x t u) fv bv m s d = let (t',s',d') = residualise' t fv bv m s d
                                           (u',s'',d'') = residualise' u fv (x:bv) m s d'
                                       in  (subst t' (abstract u' x),s'++s'',d'')
residualise' (Unfold f t) fv bv m s d = case [(f',xs,r) | (f',(xs,t',u)) <- d, r <- renamingTree t' (Unfold f t)] of
                                           ((f',xs,r):_) -> (rename r (foldl (\t x -> Apply t (Free x)) (Fun f') xs),[],d)
                                           [] -> let f' = renameVar (fv++bv++map fst d) "f"
                                                     xs = freeTree t
                                                     t' = foldl (\t x -> Apply t (Free x)) (Fun f') xs
                                                     (u,s',d') = residualise' t (f':fv) (xs++bv) ((f,t'):m) s d
                                                 in  (t',s',(f',(xs,Unfold f t,foldl abstract u xs)):d')
residualise' (Fold f e) fv bv m s d = case [t | (f',t) <- m, f==f'] of
                                         (t:_) -> let ((s',d'),e') = mapAccumL (\(s',d) (x,t) -> let (t',s'',d') = residualise' t fv bv m s d
                                                                                                 in  ((s'++s'',d'),(x,t'))) ([],d) e
                                                  in  (instantiate e' t,s',d')

-- process tree renaming

renameTree r (Var x) = case lookup x r of
                          Just x'  -> Var x'
                          Nothing -> Var x
renameTree r (Abs x t) = Abs x (renameTree r t)
renameTree r (Cons c ts) = Cons c (map (renameTree r) ts)
renameTree r (App t u) = App (renameTree r t) (renameTree r u)
renameTree r (Choice t bs) = Choice (renameTree r t) (map (\(c,xs,t) -> (c,xs,renameTree r t)) bs)
renameTree r (Gen x t u) = Gen x (renameTree r t) (renameTree r u)
renameTree r (Unfold f t) = Unfold f (renameTree r t)
renameTree r (Fold f s) = Fold f (map (Data.Bifunctor.second (renameTree r)) s)

-- free variables in a process tree

freeTree t = nub (freeTree' [] t)

freeTree' bv (Var x) = [x | x `notElem` bv]
freeTree' bv (Abs x t) = freeTree' (x:bv) t
freeTree' bv (Cons c ts) = concatMap (freeTree' bv) ts
freeTree' bv (App t u) = freeTree' bv t ++ freeTree' bv u
freeTree' bv (Choice t bs) = freeTree' bv t ++ concatMap (\(c,xs,t) -> freeTree' (xs++bv) t) bs
freeTree' bv (Gen x t u) = freeTree' bv t ++ freeTree' (x:bv) u
freeTree' bv (Unfold f t) = freeTree' bv t
freeTree' bv (Fold f s) = concatMap (\(x,t) -> freeTree' bv t) s

-- variables in a process tree

varsTree :: Tree -> [String]
varsTree t = nub (varsTree' t)

varsTree' (Var x) = [x]
varsTree' (Abs x t) = x:varsTree' t
varsTree' (Cons c ts) = concatMap varsTree' ts
varsTree' (App t u) = varsTree' t ++ varsTree' u
varsTree' (Choice t bs) = varsTree' t ++ concatMap (\(c,xs,t) -> xs++varsTree' t) bs
varsTree' (Gen x t u) = varsTree' t ++ x:varsTree' u
varsTree' (Unfold f t) = varsTree' t
varsTree' (Fold f s) = concatMap (\(x,t) -> varsTree' t) s

-- folds in a process tree

folds (Var x) = []
folds (Abs x t) = folds t
folds (Cons c ts) = concatMap folds ts
folds (App t u) = folds t ++ folds u
folds (Choice t bs) = folds t ++ concatMap (\(c,xs,t) -> folds t) bs
folds (Gen x t u) = folds t ++ folds u
folds (Unfold f t) = filter (/=f) (folds t)
folds (Fold f s) = [f]

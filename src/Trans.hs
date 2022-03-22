module Trans where

import Term
import Tree
import Exception
import Prelude hiding ((<>))
import Data.Maybe
import Data.List
import Data.Tuple

dist (t,d) = let t' = returnval (distill t EmptyCtx (free t) [] d)
                 (t'',s,d') = residualise t' []
             in  (instantiate s t'',d')
             
-- supercompiler

super (Free x) (CaseCtx k bs) fv m d = do
                                       bs' <- mapM (\(c,xs,t) -> let t' = place t k
                                                                     fv' = renameVars fv xs
                                                                     xs' = take (length xs) fv'
                                                                     u = foldr concrete (subst (Con c (map Free xs')) (abstract t' x)) xs'
                                                                 in do
                                                                    u' <- super u EmptyCtx fv' m d
                                                                    return (c,xs',u')) bs
                                       return (Choice (Var x) bs')
super (Free x) k fv m d = superCtx (Var x) k fv m d
super (Lambda x t) EmptyCtx fv m d = let x' = renameVar fv x
                                     in  do
                                         t' <- super (concrete x' t) EmptyCtx (x':fv) m d
                                         return (Abs x' t')
super (Lambda x t) (ApplyCtx k u) fv m d = super (subst u t) k fv m d
super (Lambda x t) (CaseCtx k bs) fv m d = error "Unapplied function in case selector"
super (Con c ts) EmptyCtx fv m d = do
                                   ts' <- mapM (\t -> super t EmptyCtx fv m d) ts
                                   return (Cons c ts')
super (Con c ts) (ApplyCtx k u) fv m d = error ("Constructor application is not saturated: "++show (place (Con c ts) (ApplyCtx k u)))
super (Con c ts) (CaseCtx k bs) fv m d = case find (\(c',xs,t) -> c==c' && length xs == length ts) bs of
                                            Nothing -> error ("No matching pattern in case for term:\n\n"++show (Case (Con c ts) bs))
                                            Just (c',xs,t) -> super (foldr subst t ts) k fv m d
super (Apply t u) k fv m d = super t (ApplyCtx k u) fv m d
super (Fun f) k fv m d = let t = place (Fun f) k
                         in  case [(f,t') | (f,t') <- m, embedding t' t] of
                                [] -> let f = renameVar (map fst m) "f"
                                          handler (f',t') = if   f==f'
                                                            then let (u,s1,s2) = generalise t t' fv
                                                                     fv' = map fst s1 ++ fv
                                                                 in  do
                                                                     s <- mapM (\(x,t) -> do
                                                                                          t' <- super t EmptyCtx fv' m d
                                                                                          return (x,t')) s1
                                                                     u' <- super u EmptyCtx fv' m d
                                                                     return (makeGen s u')
                                                            else throw (f',t')
                                      in  do
                                          u <- handle (super (unfold(t,d)) EmptyCtx fv ((f,t):m) d) handler
                                          return (if f `elem` folds u then Unfold f u else u)
                                m'-> case [(f,s) | (f,t') <- m', s <- inst t' t] of
                                        ((f,s):_) -> do
                                                     s' <- mapM (\(x,t) -> do
                                                                           t' <- super t EmptyCtx fv m d
                                                                           return (x,t')) s
                                                     return (Fold f s')
                                        [] -> let (f,_) = head m'
                                              in  throw (f,t)
                                
super (Case t bs) k fv m d = super t (CaseCtx k bs) fv m d

superCtx t EmptyCtx fv m d = return t
superCtx t (ApplyCtx k u) fv m d = do
                                   u' <- super u EmptyCtx fv m d
                                   superCtx (App t u') k fv m d
superCtx t (CaseCtx k bs) fv m d = do
                                   bs' <- mapM (\(c,xs,t) -> let fv' = renameVars fv xs
                                                                 xs' = take (length xs) fv'
                                                             in do
                                                                t' <- super (foldr concrete t xs') k fv' m d
                                                                return (c,xs',t')) bs
                                   return (Choice t bs')

-- distiller

distill (Free x) (CaseCtx k bs) fv m d = do
                                         bs' <- mapM (\(c,xs,t) -> let t' = place t k
                                                                       fv' = renameVars fv xs
                                                                       xs' = take (length xs) fv'
                                                                       u = foldr concrete (subst (Con c (map Free xs')) (abstract t' x)) xs'
                                                                   in do
                                                                      u' <- distill u EmptyCtx fv' m d
                                                                      return (c,xs',u')) bs
                                         return (Choice (Var x) bs')
distill (Free x) k fv m d = distillCtx (Var x) k fv m d
distill (Lambda x t) EmptyCtx fv m d = let x' = renameVar fv x
                                       in  do
                                           t' <- distill (concrete x' t) EmptyCtx (x':fv) m d
                                           return (Abs x' t')
distill (Lambda x t) (ApplyCtx k u) fv m d = distill (subst u t) k fv m d
distill (Lambda x t) (CaseCtx k bs) fv m d = error "Unapplied function in case selector"
distill (Con c ts) EmptyCtx fv m d = do
                                     ts' <- mapM (\t -> distill t EmptyCtx fv m d) ts
                                     return (Cons c ts')
distill (Con c ts) (ApplyCtx k u) fv m d = error ("Constructor application is not saturated: "++show (place (Con c ts) (ApplyCtx k u)))
distill (Con c ts) (CaseCtx k bs) fv m d = case find (\(c',xs,t) -> c==c' && length xs == length ts) bs of
                                              Nothing -> error ("No matching pattern in case for term:\n\n"++show (Case (Con c ts) bs))
                                              Just (c',xs,t) -> distill (foldr subst t ts) k fv m d
distill (Apply t u) k fv m d = distill t (ApplyCtx k u) fv m d
distill (Fun f) k fv m d = let t = returnval (super (Fun f) k fv [] d)
                           in  case [(f,s) | (f,t') <- m, s <- instTree t' t] of
                                  ((f,s):_) -> return (Fold f s)
                                  [] -> case [(f,t') | (f,t') <- m, embeddingTree t' t] of
                                           ((f,t'):_) -> throw (f,t') 
                                           [] -> let f = renameVar (map fst m) "f"
                                                     (t',s',d') = residualise t []
                                                     handler (f',t') = if   f==f'
                                                                       then let (u,s1,s2) = generaliseTree t t'
                                                                            in  if   null s1
                                                                                then return u 
                                                                                else let (u',s',d') = residualise u s1
                                                                                     in  do
                                                                                         s'' <- mapM (\(x,t) -> do
                                                                                                                t' <- distill t EmptyCtx fv m d'
                                                                                                                return (x,t')) s'
                                                                                         u' <- distill u' EmptyCtx (map fst s''++fv) m d'
                                                                                         return (makeGen s'' u')
                                                                       else throw (f',t')
                                                 in  do
                                                     u <- handle (distill (unfold(t',d')) EmptyCtx fv ((f,t):m) d') handler
                                                     return (if f `elem` folds u  then Unfold f u else u)                              
distill (Case t bs) k fv m d = distill t (CaseCtx k bs) fv m d

distillCtx t EmptyCtx fv m d = return t
distillCtx t (ApplyCtx k u) fv m d = do
                                     u' <- distill u EmptyCtx fv m d
                                     distillCtx (App t u') k fv m d
distillCtx t (CaseCtx k bs) fv m d = do
                                     bs' <- mapM (\(c,xs,t) -> let fv' = renameVars fv xs
                                                                   xs' = take (length xs) fv'
                                                               in do
                                                                  t' <- distill (foldr concrete t xs') k fv' m d
                                                                  return (c,xs',t')) bs
                                     return (Choice t bs')
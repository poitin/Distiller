module Trans where

import Term
import Exception
import Prelude hiding ((<>))
import Data.Maybe
import Data.List
import Data.Tuple
import Debug.Trace

dist (t,d) = let t' = returnval (trans 2 t EmptyCtx (free t) [] d)
             in  residualise (t',d)
         
-- level n transformer

trans 0 t k fv m d = return (place t k)
trans n t k fv m d = trans' n t k fv m d

trans' n (Free x) (CaseCtx k bs) fv m d = do
                                         bs' <- mapM (\(c,xs,t) -> let t' = place t k
                                                                       fv' = renameVars fv xs
                                                                       xs' = take (length xs) fv'
                                                                       u = foldr concrete (subst (Con c (map Free xs')) (abstract t' x)) xs'
                                                                   in do
                                                                      u' <- trans n u EmptyCtx fv' m d
                                                                      return (c,xs,foldl abstract u' xs')) bs
                                         return (Case (Free x) bs')
trans' n (Free x) k fv m d = transCtx n (Free x) k fv m d
trans' n (Lambda x t) EmptyCtx fv m d = let x' = renameVar fv x
                                        in do
                                           t' <- trans n (concrete x' t) EmptyCtx (x':fv) m d
                                           return (Lambda x (abstract t' x'))
trans' n (Lambda x t) (ApplyCtx k u) fv m d = trans n (subst u t) k fv m d
trans' n (Lambda x t) (CaseCtx k bs) fv m d = error "Unapplied function in case selector"
trans' n (Con c ts) EmptyCtx fv m d = do
                                     ts' <- mapM (\t -> trans n t EmptyCtx fv m d) ts
                                     return (Con c ts')
trans' n (Con c ts) (ApplyCtx k u) fv m d = error ("Constructor application is not saturated: "++show (place (Con c ts) (ApplyCtx k u)))
trans' n (Con c ts) (CaseCtx k bs) fv m d = case find (\(c',xs,t) -> c==c' && length xs == length ts) bs of
                                              Nothing -> error ("No matching pattern in case for term:\n\n"++show (Case (Con c ts) bs))
                                              Just (c',xs,t) -> trans n (foldr subst t ts) k fv m d
trans' n (Apply t u) k fv m d = trans n t (ApplyCtx k u) fv m d
trans' n (Fun f) k fv m d | f `notElem` map fst d = return (place (Fun f) k)
trans' n (Fun f) k fv m d = let t = returnval (trans (n-1) (Fun f) k fv [] d)
                            in  case [(f,xs,s) | (f,(xs,t')) <- m, s <- inst t' t] of
                                   ((f,xs,s):_) -> do
                                                   s' <- mapM (\(x,t) -> let (t',d') = residualise (t,d)
                                                                         in  do
                                                                             t'' <- trans n t' EmptyCtx fv m d'
                                                                             return (x,t'')) s
                                                   return (Fold (instantiate s' (foldl (\t x -> Apply t (Free x)) (Fun f) xs)))
                                   [] -> case [(f,r) | (f,(xs,t')) <- m, r <- embedding t' t] of
                                            ((f,r):_) -> throw (f,t,r)
                                            [] -> let f = renameVar (map fst m ++ map fst d) "f"
                                                      xs = free t
                                                      t' = foldl (\t x -> Apply t (Free x)) (Fun f) xs
                                                      (u,d') = residualise (t,d)
                                                      handler (f',u',r) = if   f==f'
                                                                          then let t'' = generaliseTree t u' r
                                                                                   (u'',d') = residualise (t'',d)
                                                                               in  trans n u'' EmptyCtx fv m d'
                                                                          else throw (f',u',r)
                                                  in  do
                                                      u' <- handle (trans n (unfold(u,d')) EmptyCtx fv ((f,(xs,t)):m) d') handler
                                                      return (if redex t' `elem` folds u' then Unfold t' u' else u')
trans' n (Case t bs) k fv m d = trans n t (CaseCtx k bs) fv m d
trans' n (Let x t u) k fv m d = let x' = renameVar fv x
                                in  do
                                    t' <- trans n t EmptyCtx fv m d
                                    u' <- trans n (concrete x' u) k (x':fv) m d
                                    return (Let x t' (abstract u' x'))

transCtx n t EmptyCtx fv m d = return t
transCtx n t (ApplyCtx k u) fv m d = do
                                     u' <- trans n u EmptyCtx fv m d
                                     transCtx n (Apply t u') k fv m d
transCtx n t (CaseCtx k bs) fv m d = do
                                     bs' <- mapM (\(c,xs,t) -> let fv' = renameVars fv xs
                                                                   xs' = take (length xs) fv'
                                                               in do
                                                                  t' <- trans n (foldr concrete t xs') k fv' m d
                                                                  return (c,xs,foldl abstract t' xs')) bs
                                     return (Case t bs')
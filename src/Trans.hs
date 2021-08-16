module Trans where

import Term
import Exception
import Prelude hiding ((<>))
import Data.Maybe
import Data.List

dist (t,d) = let e = map (processFun d) d
                 t' = returnval (trans 2 t EmptyCtx (free t) [] d e)
                 (t'',d',e') = residualise t' d e
             in  (t'',d')

-- level n transformer

trans 0 t k fv m d e = return (place t k)

trans n (Free x) (CaseCtx k bs) fv m d e = do
                                           bs' <- mapM (\(c,xs,t) -> let t' = place t k
                                                                         fv' = renameVars fv xs
                                                                         xs' = take (length xs) fv'
                                                                         u = foldr concrete (subst (Con c (map Free xs')) (abstract t' x)) xs'
                                                                     in do
                                                                        u' <- trans n u EmptyCtx fv' m d e
                                                                        return (c,xs,foldl abstract u' xs')) bs
                                           return (Case (Free x) bs')
trans n (Free x) k fv m d e = transCtx n (Free x) k fv m d e
trans n (Lambda x t) EmptyCtx fv m d e = let x' = renameVar fv x
                                         in do
                                            t' <- trans n (concrete x' t) EmptyCtx (x':fv) m d e
                                            return (Lambda x (abstract t' x'))
trans n (Lambda x t) (ApplyCtx k u) fv m d e = trans n (subst u t) k fv m d e
trans n (Lambda x t) (CaseCtx k bs) fv m d e = error "Unapplied function in case selector"
trans n (Con c ts) EmptyCtx fv m d e = do
                                       ts' <- mapM (\t -> trans n t EmptyCtx fv m d e) ts
                                       return (Con c ts')
trans n (Con c ts) (ApplyCtx k u) fv m d e = error ("Constructor application is not saturated: "++show (place (Con c ts) (ApplyCtx k u)))
trans n (Con c ts) (CaseCtx k bs) fv m d e = case find (\(c',xs,t) -> c==c' && length xs == length ts) bs of
                                                Nothing -> error ("No matching pattern in case for term:\n\n"++show (Case (Con c ts) bs))
                                                Just (c',xs,t) -> trans n (foldr subst t ts) k fv m d e
trans n (Apply t u) k fv m d e = trans n t (ApplyCtx k u) fv m d e
trans n (Fun f) k fv m d e = let t = returnval (trans (n-1) (Fun f) k fv [] d e)
                                 (t',d',e') = residualise t d e
                              in  case [(l,u,s) | (l,u) <- m, s <- inst u t'] of
                                     ((l,u,s):ls) -> do
                                                     s' <- mapM (\(x,t) -> do
                                                                           t' <- trans n t EmptyCtx fv m d e
                                                                           return (x,t')) s
                                                     return (makeLet' s' (Fold l u))
                                     [] -> case [l | (l,u) <- m, isEmbedding u t'] of
                                              (l:ls) -> throw (l,t')
                                              [] -> let l = renameVar (map fst m) "l"
                                                        handler (l',u) = if   l==l'
                                                                         then let (u',s1,s2) = generaliseTerm t' u
                                                                              in  trans n (makeLet s1 u') EmptyCtx fv m d' e'
                                                                         else throw (l',u)
                                                    in  do
                                                        u <- handle (trans n (unfold(t',d')) EmptyCtx fv ((l,t'):m) d' e') handler
                                                        return (if l `elem` folds u then Unfold l t' u else u)
trans n (Case t bs) k fv m d e = trans n t (CaseCtx k bs) fv m d e
trans n (Let x t u) k fv m d e = let x' = renameVar fv x
                                 in do
                                    t' <- trans n t EmptyCtx fv m d e
                                    u' <- trans n (concrete x' u) k (x':fv) m d e
                                    return (Let x t' (abstract u' x'))

transCtx n t EmptyCtx fv m d e = return t
transCtx n t (ApplyCtx k u) fv m d e = do
                                       u' <- trans n u EmptyCtx fv m d e
                                       transCtx n (Apply t u') k fv m d e
transCtx n t (CaseCtx k bs) fv m d e = do
                                       bs' <- mapM (\(c,xs,t) -> let fv' = renameVars fv xs
                                                                     xs' = take (length xs) fv'
                                                                 in do
                                                                    t' <- trans n (foldr concrete t xs') k fv' m d e
                                                                    return (c,xs,foldl abstract t' xs')) bs
                                       return (Case t bs')

-- Program residualisation

residualise t = residualise' [] t (free t)

residualise' ls (Free x) fv d e = (Free x,d,e)
residualise' ls (Bound i) fv d e = (Bound i,d,e)
residualise' ls (Lambda x t) fv d e = let x' = renameVar fv x
                                          (t',d',e') = residualise' ls (concrete x' t) (x':fv) d e
                                      in  (Lambda x (abstract t' x'),d',e')
residualise' ls (Con c ts) fv d e = let ((d',e'),ts') = mapAccumL (\(d,e) t -> let (t',d',e') = residualise' ls t fv d e
                                                                               in  ((d',e'),t')) (d,e) ts
                                    in  (Con c ts',d',e')
residualise' ls (Apply t u) fv d e = let (t',d',e') = residualise' ls t fv d e
                                         (u',d'',e'') = residualise' ls u fv d' e'
                                     in  (Apply t' u',d'',e'')
residualise' ls (Fun f) fv d e = (Fun f,d,e)
residualise' ls (Case t bs) fv d e = let (t',d',e') = residualise' ls t fv d e
                                         ((d'',e''),bs') = mapAccumL (\(d,e) (c,xs,t) -> let fv' = renameVars fv xs
                                                                                             xs' = take (length xs) fv'
                                                                                             (t',d',e') = residualise' ls (foldr concrete t xs') fv' d e
                                                                                         in  ((d',e'),(c,xs,foldl abstract t' xs'))) (d',e') bs
                                     in  (Case t' bs',d'',e'')
residualise' ls (Let x t u) fv d e = let x' = renameVar fv x
                                         (t',d',e') = residualise' ls t fv d e
                                         (u',d'',e'') = residualise' ls (concrete x' u) (x':fv) d' e'
                                     in  (subst t' (abstract u' x'),d'',e'')
residualise' ls t'@(Unfold l t u) fv d e = case [rename r u | (u,u') <- e, r <- funRenaming u' t'] of
                                              (t:ts) -> (t,d,e)
                                              [] -> case [rename r u' | (u,u') <- e, r <- funEmbedding u' t'] of
                                                       (t:ts) -> let (t'',s1,s2) = funGeneralise t t'
                                                                 in  residualise' ls (makeLet s2 t'') fv d e
                                                       [] -> let f = renameVar (fv ++ map fst d) "f"
                                                                 xs = free u
                                                                 t'' = foldl (\t x -> Apply t (Free x)) (Fun f) xs
                                                                 (u',d',e') = residualise' ((l,(t'',t)):ls) u (f:fv) d e
                                                             in  (t'',(f,(xs,foldl abstract u' xs)):d',(t'',t'):e')
residualise' ls (Fold l t) fv d e = case [instantiate s t' | (l',(t',u)) <- ls, l==l', s <- inst u t] of
                                       (t:ts) -> (t,d,e)
                                       [] -> residualise' ls t fv d e
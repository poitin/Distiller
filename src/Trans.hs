module Trans where

import Term
import Exception
import Data.List
import Data.Maybe
import Debug.Trace

super t (ApplyCtx k []) fv m d = super t k fv m d
super (Free x) (CaseCtx k bs) fv m d = do
                                       bs' <- mapM (\(c,xs,t) -> let t' = place t k
                                                                     fv' = foldr (\x fv -> let x' = rename fv x in x':fv) fv xs
                                                                     xs' = take (length xs) fv'
                                                                     u = subst (Con c (map Free xs')) (abstract (foldr concrete t' xs') x)
                                                                 in do
                                                                    u' <- super u EmptyCtx fv' m d
                                                                    return (c,xs,foldl abstract u' xs')) bs
                                       return (Case (Free x) bs')
super (Free x) k fv m d = superCtx (Free x) k fv m d
super (Lambda x t) EmptyCtx fv m d = let x' = rename fv x
                                     in do
                                        t' <- super (concrete x' t) EmptyCtx (x':fv) m d
                                        return (Lambda x (abstract t' x'))
super (Lambda x t) (ApplyCtx k (t':ts)) fv m d = super (subst t' t) (ApplyCtx k ts) fv m d
super (Lambda x t) (CaseCtx k bs) fv m d = error "Unapplied function in case selector"
super (Con c ts) EmptyCtx fv m d = do
                                   ts' <- mapM (\t -> super t EmptyCtx fv m d) ts
                                   return (Con c ts')
super (Con c ts) (ApplyCtx k ts') fv m d = error ("Constructor application is not saturated: "++show (place (Con c ts) (ApplyCtx k ts')))
super (Con c ts) (CaseCtx k bs) fv m d = case find (\(c',xs,t) -> c==c' && length xs == length ts) bs of
                                            Nothing -> error ("No matching pattern in case for term:\n\n"++show (Case (Con c ts) bs))
                                            Just (c',xs,t) -> super (foldr subst t ts) k fv m d
super (Fun f) k fv m d | f `notElem` fst(unzip d) = superCtx (Fun f) k fv m d
super (Fun f) k fv m d = let t = place (Fun f) k
                         in case find (\(f,(xs,t')) -> isJust (inst t' t)) m of
                               Just (f,(xs,t')) -> let Just s = inst t' t
                                                   in  super (makeLet s (Apply (Fun f) (map Free xs))) EmptyCtx fv m d
                               Nothing -> case find (\(f,(xs,t')) -> not (null (embed t' t))) m of
                                             Just (f,_) -> throw (f,t)
                                             Nothing -> let fs = fst(unzip(m++d))
                                                            f = rename fs "f"
                                                            xs = free t
                                                            (t',d') = unfold t (f:fs) d
                                                            handler (f',t') = if   f==f'
                                                                              then let (t'',s1,s2) = generalise t t'
                                                                                   in  super (makeLet s1 t'') EmptyCtx fv m d
                                                                              else throw (f',t')
                                                        in  do t'' <- handle (super t' EmptyCtx fv ((f,(xs,t)):m) d') handler
                                                               return (if f `elem` funs t'' then Letrec f xs (foldl abstract (abstractFun t'' f) xs) (Apply (Bound 0) (map Free xs)) else t'')

super (Apply t ts) k fv m d = super t (ApplyCtx k ts) fv m d
super (Case t bs) k fv m d = super t (CaseCtx k bs) fv m d
super (Let x t u) k fv m d = let x' = rename fv x
                             in do
                                t' <- super t EmptyCtx fv m d
                                u' <- super (concrete x' u) k (x':fv) m d
                                return (subst t' (abstract u' x'))
super (Letrec f xs t u) k fv m d = let f' = rename (fst(unzip(m++d))) f
                                       t' = concreteFun f' (foldr concrete t xs)
                                       u' = concreteFun f' u
                                   in  super u' k fv m ((f',(xs,t')):d)


superCtx t EmptyCtx fv m d = return t
superCtx t (ApplyCtx k ts) fv m d = do
                                    ts' <- mapM (\t -> super t EmptyCtx fv m d) ts
                                    superCtx (Apply t ts') k fv m d
superCtx t (CaseCtx k bs) fv m d = do
                                   bs' <- mapM (\(c,xs,t) -> let fv' = foldr (\x fv -> let x' = rename fv x in x':fv) fv xs
                                                                 xs' = take (length xs) fv'
                                                             in do
                                                                t' <- super (foldr concrete t xs') k fv' m d
                                                                return (c,xs,foldl abstract t' xs')) bs
                                   return (Case t bs')
                                   
dist (t,d) = returnval (distill t EmptyCtx (free t) [] d)

distill t k fv = trace (show fv ++ show (place t k)) distill' t k fv
distill' t (ApplyCtx k []) fv m d = distill t k fv m d
distill' (Free x) (CaseCtx k bs) fv m d = do
                                         bs' <- mapM (\(c,xs,t) -> let t' = place t k
                                                                       fv' = foldr (\x fv -> let x' = rename fv x in x':fv) fv xs
                                                                       xs' = take (length xs) fv'
                                                                       u = subst (Con c (map Free xs')) (abstract (foldr concrete t' xs') x)
                                                                   in do
                                                                      u' <- distill u EmptyCtx fv' m d
                                                                      return (c,xs,foldl abstract u' xs')) bs
                                         return (Case (Free x) bs')
distill' (Free x) k fv m d = distillCtx (Free x) k fv m d
distill' (Lambda x t) EmptyCtx fv m d = let x' = rename fv x
                                       in do
                                          t' <- distill (concrete x' t) EmptyCtx (x':fv) m d
                                          return (Lambda x (abstract t' x'))
distill' (Lambda x t) (ApplyCtx k (t':ts)) fv m d = distill (subst t' t) (ApplyCtx k ts) fv m d
distill' (Lambda x t) (CaseCtx k bs) fv m d = error "Unapplied function in case selector"
distill' (Con c ts) EmptyCtx fv m d = do
                                     ts' <- mapM (\t -> distill t EmptyCtx fv m d) ts
                                     return (Con c ts')
distill' (Con c ts) (ApplyCtx k ts') fv m d = error ("Constructor application is not saturated: "++show (place (Con c ts) (ApplyCtx k ts')))
distill' (Con c ts) (CaseCtx k bs) fv m d = case find (\(c',xs,t) -> c==c' && length xs == length ts) bs of
                                              Nothing -> error ("No matching pattern in case for term:\n\n"++show (Case (Con c ts) bs))
                                              Just (c',xs,t) -> distill (foldr subst t ts) k fv m d
distill' (Fun f) k fv m d | f `notElem` fst(unzip d) = distillCtx (Fun f) k fv m d
distill' (Fun f) k fv m d = let t = returnval (super (Fun f) k fv [] d)
                            in  case find (\(f,(xs,t')) -> isJust (inst t' t)) m of
                                   Just (f,(xs,t')) -> let Just s = inst t' t
                                                       in  return (instantiate s (Apply (Fun f) (map Free xs)))
                                   Nothing -> case find (\(f,(xs,t')) -> not (null (embed t' t))) m of
                                                 Just (f,_) -> throw (f,t)
                                                 Nothing -> let fs = fst(unzip (m++d))
                                                                f = rename fs "f"
                                                                xs = free t
                                                                (t',d') = unfold t (f:fs) d
                                                                handler (f',t') = if   f==f'
                                                                                  then let (t'',s1,s2) = generalise t t'
                                                                                       in  distill (makeLet s1 t'') EmptyCtx fv m d
                                                                                  else throw (f',t')
                                                            in  do t'' <- handle (distill t' EmptyCtx fv ((f,(xs,t)):m) d') handler
                                                                   return (if f `elem` funs t'' then Letrec f xs (foldl abstract (abstractFun t'' f) xs) (Apply (Bound 0) (map Free xs)) else t'')
distill' (Apply t ts) k fv m d = distill t (ApplyCtx k ts) fv m d
distill' (Case t bs) k fv m d = distill t (CaseCtx k bs) fv m d
distill' (Let x t u) k fv m d = let x' = rename fv x
                               in do
                                  t' <- distill t EmptyCtx fv m d
                                  u' <- distill (concrete x' u) k (x':fv) m d
                                  return (subst t' (abstract u' x'))
distill' (Letrec f xs t u) k fv m d = let f' = rename (fst(unzip(m++d))) f
                                          t' = concreteFun f' (foldr concrete t xs)
                                          u' = concreteFun f' u
                                      in  distill u' k fv m ((f',(xs,t')):d)
distillCtx t EmptyCtx fv m d = return t
distillCtx t (ApplyCtx k ts) fv m d = do
                                     ts' <- mapM (\t -> distill t EmptyCtx fv m d) ts
                                     distillCtx (Apply t ts') k fv m d
distillCtx t (CaseCtx k bs) fv m d = do
                                     bs' <- mapM (\(c,xs,t) -> let fv' = foldr (\x fv -> let x' = rename fv x in x':fv) fv xs
                                                                   xs' = take (length xs) fv'
                                                               in do
                                                                  t' <- distill (foldr concrete t xs') k fv' m d
                                                                  return (c,xs,foldl abstract t' xs')) bs
                                     return (Case t bs')



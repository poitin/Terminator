module Transform where

import Term

import Data.List
import Data.Maybe
import Debug.Trace

sup (t,d) = super t EmptyCtx (free t) [] d

super (Free x) (CaseCtx k bs) fv m d = let bs' = map (\(c,xs,t) -> let t' = place t k
                                                                       fv' = foldr (\x fv -> let x' = rename fv x in x':fv) fv xs
                                                                       xs' = take (length xs) fv'
                                                                       u = subst (Con c (map Free xs')) (abstract (foldr concrete t' xs') x)
                                                                       u' = super u EmptyCtx fv' m d
                                                                   in (c,xs,foldl abstract u' xs')) bs
                                       in Case (Free x) bs'
super (Free x) k fv m d = superCtx (Free x) k fv m d
super (Lambda x t) EmptyCtx fv m d = let x' = rename fv x
                                         t' = super (concrete x' t) EmptyCtx (x':fv) m d
                                     in Lambda x (abstract t' x')
super (Lambda x t) (ApplyCtx k u) fv m d = super (subst u t) k fv m d
super (Lambda x t) (CaseCtx k bs) fv m d = error "Unapplied function in case selector"
super (Con c ts) EmptyCtx fv m d = let ts' = map (\t -> super t EmptyCtx fv m d) ts
                                   in Con c ts'
super (Con c ts) (ApplyCtx k t) fv m d = error ("Constructor application is not saturated: "++show (place (Con c ts) (ApplyCtx k t)))
super (Con c ts) (CaseCtx k bs) fv m d = case find (\(c',xs,t) -> c==c' && length xs == length ts) bs of
                                            Nothing -> error ("No matching pattern in case for term:\n\n"++show (Case (Con c ts) bs))
                                            Just (c',xs,t) -> super (foldr subst t ts) k fv m d
super (Apply t u) k fv m d = super t (ApplyCtx k u) fv m d
super t@(Call f _) k fv m d | f `notElem` fst(unzip d) = superCtx t k fv m d
super t@(Call _ _) k fv m d = let t' = place t k
                              in case find (\(f,(xs,u)) -> isJust (inst u t')) m of
                                    Just (f,(xs,u)) -> let Just s = inst u t'
                                                       in  super (makeLet s (Call f (map Free xs))) EmptyCtx fv m d
                                    Nothing -> case find (\(f,(xs,u)) -> not (null (embed u t'))) m of
                                                  Just (f,(xs,u)) -> let (u',s1,s2) = generalise u t'
                                                                     in  super (makeLet s2 u') EmptyCtx fv m d
                                                  Nothing -> let fs = fst (unzip (m++d))
                                                                 f' = rename fs "f"
                                                                 xs = free t'
                                                                 (u,d') = unfold t' (f':fs) d
                                                                 u' = super u EmptyCtx fv ((f',(xs,t')):m) d'
                                                             in if f' `elem` funs u' then Letrec f' xs (foldl abstract u' xs) (Call f' (map Free xs)) else u'
super (Case t bs) k fv m d = super t (CaseCtx k bs) fv m d
super (Let x t u) k fv m d = let x' = rename fv x
                                 t' = super t EmptyCtx fv m d
                                 u' = super (concrete x' u) k (x':fv) m d
                             in subst t' (abstract u' x')
super (Letrec f xs t u) k fv m d = let f' = rename (fst (unzip (m++d))) f
                                       t' = foldr concrete (renameFun f f' t) xs
                                       u' = renameFun f f' u
                                   in  super u' k fv m ((f',(xs,t')):d)

superCtx t EmptyCtx fv m d = t
superCtx t (ApplyCtx k u) fv m d = let u' = super u EmptyCtx fv m d
                                   in superCtx (Apply t u') k fv m d
superCtx t (CaseCtx k bs) fv m d = let bs' = map (\(c,xs,t) -> let fv' = foldr (\x fv -> let x' = rename fv x in x':fv) fv xs
                                                                   xs' = take (length xs) fv'
                                                                   t' = super (foldr concrete t xs') k fv' m d
                                                               in (c,xs,foldl abstract t' xs')) bs
                                   in Case t bs'

dist (t,d) = distill t EmptyCtx (free t) [] d

distill (Free x) (CaseCtx k bs) fv m d = let bs' = map (\(c,xs,t) -> let t' = place t k
                                                                         fv' = foldr (\x fv -> let x' = rename fv x in x':fv) fv xs
                                                                         xs' = take (length xs) fv'
                                                                         u = subst (Con c (map Free xs')) (abstract (foldr concrete t' xs') x)
                                                                         u' = distill u EmptyCtx fv' m d
                                                                     in (c,xs,foldl abstract u' xs')) bs
                                         in Case (Free x) bs'
distill (Free x) k fv m d = distillCtx (Free x) k fv m d
distill (Lambda x t) EmptyCtx fv m d = let x' = rename fv x
                                           t' = distill (concrete x' t) EmptyCtx (x':fv) m d
                                       in Lambda x (abstract t' x')
distill (Lambda x t) (ApplyCtx k u) fv m d = distill (subst u t) k fv m d
distill (Lambda x t) (CaseCtx k bs) fv m d = error "Unapplied function in case selector"
distill (Con c ts) EmptyCtx fv m d = let ts' = map (\t -> distill t EmptyCtx fv m d) ts
                                     in Con c ts'
distill (Con c ts) (ApplyCtx k t) fv m d = error ("Constructor application is not saturated: "++show (place (Con c ts) (ApplyCtx k t)))
distill (Con c ts) (CaseCtx k bs) fv m d = case find (\(c',xs,t) -> c==c' && length xs == length ts) bs of
                                              Nothing -> error ("No matching pattern in case for term:\n\n"++show (Case (Con c ts) bs))
                                              Just (c',xs,t) -> distill (foldr subst t ts) k fv m d
distill (Apply t u) k fv m d = distill t (ApplyCtx k u) fv m d
distill t@(Call f _) k fv m d | f `notElem` fst(unzip d) = distillCtx t k fv m d
distill t@(Call _ _) k fv m d = let t' = super t k fv [] d
                                in case find (\(f,(xs,u)) -> isJust (inst u t')) m of
                                      Just (f,(xs,u)) -> let Just s = inst u t'
                                                         in  instantiate s (Call f (map Free xs))
                                      Nothing -> case find (\(f,(xs,u)) -> not (null (embed u t'))) m of
                                                    Just (f,(xs,u)) -> let (u',s1,s2) = generalise u t'
                                                                           u'' = distill u' EmptyCtx (fst(unzip s2)++fv) m d
                                                                       in instantiate s2 u''
                                                    Nothing -> let fs = fst (unzip (m++d))
                                                                   f = rename fs "f"
                                                                   xs = free t'
                                                                   (u,d') = unfold t' (f:fs) d
                                                                   u' = distill u EmptyCtx fv ((f,(xs,t')):m) d'
                                                               in if f `elem` funs u' then Letrec f xs (foldl abstract u' xs) (Call f (map Free xs)) else u'
distill (Case t bs) k fv m d = distill t (CaseCtx k bs) fv m d
distill (Let x t u) k fv m d = let x' = rename fv x
                                   t' = distill t EmptyCtx fv m d
                                   u' = distill (concrete x' u) k (x':fv) m d
                               in subst t' (abstract u' x')
distill (Letrec f xs t u) k fv m d = let f' = rename (fst (unzip (m++d))) f
                                         t' = foldr concrete (renameFun f f' t) xs
                                         u' = renameFun f f' u
                                     in  distill u' k fv m ((f',(xs,t')):d)

distillCtx t EmptyCtx fv m d = t
distillCtx t (ApplyCtx k u) fv m d = let u' = distill u EmptyCtx fv m d
                                     in distillCtx (Apply t u') k fv m d
distillCtx t (CaseCtx k bs) fv m d = let bs' = map (\(c,xs,t) -> let fv' = foldr (\x fv -> let x' = rename fv x in x':fv) fv xs
                                                                     xs' = take (length xs) fv'
                                                                     t' = distill (foldr concrete t xs') k fv' m d
                                                                 in (c,xs,foldl abstract t' xs')) bs
                                     in Case t bs'


transform n (t,d) = trans n t EmptyCtx (free t) [] d

trans 0 t k fv m d = place t k
trans n (Free x) (CaseCtx k bs) fv m d = let bs' = map (\(c,xs,t) -> let t' = place t k
                                                                         fv' = foldr (\x fv -> let x' = rename fv x in x':fv) fv xs
                                                                         xs' = take (length xs) fv'
                                                                         u = subst (Con c (map Free xs')) (abstract (foldr concrete t' xs') x)
                                                                         u' = trans n u EmptyCtx fv' m d
                                                                     in (c,xs,foldl abstract u' xs')) bs
                                         in Case (Free x) bs'
trans n (Free x) k fv m d = transCtx n (Free x) k fv m d
trans n (Lambda x t) EmptyCtx fv m d = let x' = rename fv x
                                           t' = trans n (concrete x' t) EmptyCtx (x':fv) m d
                                       in Lambda x (abstract t' x')
trans n (Lambda x t) (ApplyCtx k u) fv m d = trans n (subst u t) k fv m d
trans n (Lambda x t) (CaseCtx k bs) fv m d = error "Unapplied function in case selector"
trans n (Con c ts) EmptyCtx fv m d = let ts' = map (\t -> trans n t EmptyCtx fv m d) ts
                                     in Con c ts'
trans n (Con c ts) (ApplyCtx k t) fv m d = error ("Constructor application is not saturated: "++show (place (Con c ts) (ApplyCtx k t)))
trans n (Con c ts) (CaseCtx k bs) fv m d = case find (\(c',xs,t) -> c==c' && length xs == length ts) bs of
                                              Nothing -> error ("No matching pattern in case for term:\n\n"++show (Case (Con c ts) bs))
                                              Just (c',xs,t) -> trans n (foldr subst t ts) k fv m d
trans n (Apply t u) k fv m d = trans n t (ApplyCtx k u) fv m d
trans n t@(Call f _) k fv m d | f `notElem` fst(unzip d) = transCtx n t k fv m d
trans n t@(Call _ _) k fv m d = let t' = trans (n-1) t k fv [] d
                                in case find (\(f,(xs,u)) -> isJust (inst u t')) m of
                                      Just (f,(xs,u)) -> let Just s = inst u t'
                                                         in  instantiate s (Call f (map Free xs))
                                      Nothing -> case find (\(f,(xs,u)) -> not (null (embed u t'))) m of
                                                    Just (f,(xs,u)) -> let (u',s1,s2) = generalise u t'
                                                                           u'' = trans n u' EmptyCtx (fst(unzip s2)++fv) m d
                                                                       in instantiate s2 u''
                                                    Nothing -> let fs = fst (unzip (m++d))
                                                                   f = rename fs "f"
                                                                   xs = free t'
                                                                   (u,d') = unfold t' (f:fs) d
                                                                   u' = trans n u EmptyCtx fv ((f,(xs,t')):m) d'
                                                               in if f `elem` funs u' then Letrec f xs (foldl abstract u' xs) (Call f (map Free xs)) else u'
trans n (Case t bs) k fv m d = trans n t (CaseCtx k bs) fv m d
trans n (Let x t u) k fv m d = let x' = rename fv x
                                   t' = trans n t EmptyCtx fv m d
                                   u' = trans n (concrete x' u) k (x':fv) m d
                               in subst t' (abstract u' x')
trans n (Letrec f xs t u) k fv m d = let f' = rename (fst (unzip (m++d))) f
                                         t' = foldr concrete (renameFun f f' t) xs
                                         u' = renameFun f f' u
                                     in  trans n u' k fv m ((f',(xs,t')):d)

transCtx n t EmptyCtx fv m d = t
transCtx n t (ApplyCtx k u) fv m d = let u' = trans n u EmptyCtx fv m d
                                     in transCtx n (Apply t u') k fv m d
transCtx n t (CaseCtx k bs) fv m d = let bs' = map (\(c,xs,t) -> let fv' = foldr (\x fv -> let x' = rename fv x in x':fv) fv xs
                                                                     xs' = take (length xs) fv'
                                                                     t' = trans n (foldr concrete t xs') k fv' m d
                                                                 in (c,xs,foldl abstract t' xs')) bs
                                     in Case t bs'

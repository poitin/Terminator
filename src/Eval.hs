module Eval where

import Term
import Data.List
import Debug.Trace

eval (Free x) k d r a = error ("Unbound identifier: "++x)
eval (Lambda x t) EmptyCtx d r a = (Lambda x t,r,a)
eval (Lambda x t) (ApplyCtx k u) d r a = eval (subst u t) k d (r+1) a
eval (Lambda x t) (CaseCtx k bs) d r a = error ("Unapplied function in case selector: " ++ show (Lambda x t))
eval (Con c ts) EmptyCtx d r a = let ((r',a'),ts') = mapAccumL (\(r,a) t -> let (t',r',a') = eval t EmptyCtx d r a
                                                                            in  ((r',a'),t')) (r,a) ts
                                 in  (Con c ts',r'+1,a'+1)
eval (Con c ts) (ApplyCtx k t) d r a = error ("Constructor application is not saturated: "++show (place (Con c ts) (ApplyCtx k t)))
eval (Con c ts) (CaseCtx k bs) d r a = case find (\(c',xs,t) -> c==c' && length xs == length ts) bs of
                                          Nothing -> error ("No matching pattern in case for term:\n\n"++show (Case (Con c ts) bs))
                                          Just (c',xs,t) -> eval (foldr subst t ts) k d (r+length ts) a
eval (Apply t u) k d r a = eval t (ApplyCtx k u) d r a
eval (Call f ts) k d r a = case lookup f d of
                              Nothing -> error ("Undefined function: "++f)
                              Just (xs,t)  -> eval (foldl Apply (foldr Lambda t xs) ts) k d (r+1) a
eval (Case t bs) k d r a = eval t (CaseCtx k bs) d r a
eval (Let x t u) k d r a = eval (subst t u) k d (r+1) a
eval (Letrec f xs t ts) k d r a = let f' = rename (fst (unzip d)) f
                                      t' = renameFun f f' t
                                  in  eval (Call f' ts) k ((f',(xs,t')):d) (r+1) a

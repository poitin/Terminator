module Termcheck where

import Exception
import Term
import Trans
import Data.List
import Data.Maybe

check (t,d) = let t' =  returnval (distill t EmptyCtx (free t) [] [] d)
              in  check' [] (free t') t'

check' fs fv (Free x) = True
check' fs fv (Bound i) = True
check' fs fv (Lambda x t) = let x' = renameVar fv x
                            in  check' fs (x':fv) (concrete x' t)
check' fs fv (Con c ts) = all (check' fs fv) ts
check' fs fv (Apply t u) = check' fs fv t && check' fs fv u
check' fs fv (Case (Free x) bs) = all (\(c,xs,t) -> let fv' = renameVars fv xs
                                                        xs' = take (length xs) fv'
                                                    in  check' (add x fs) fv' (foldr concrete t xs')) bs
check' fs fv (Case t bs) = check' fs fv t && all (\(c,xs,t) -> let fv' = renameVars fv xs
                                                                   xs' = take (length xs) fv'
                                                               in  check' fs fv' (foldr concrete t xs')) bs
check' fs fv (Let x t u) = check' fs fv t && check' fs fv u
check' fs fv (Unfold t u) = let f = renameVar (map fst fs) "f"
                                xs = free u
                            in  check' ((f,(xs,[])):fs) fv (concrete f u)
check' fs fv (Fold (Free f) u) = case lookup f fs of
                                    Nothing -> error "Unmatched fold"
                                    Just (xs,cs) -> not (null (xs `intersect` cs))

add x = map (\(f,(xs,cs)) -> (f,(xs,x:cs)))

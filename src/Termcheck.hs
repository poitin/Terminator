module Termcheck where

import Term
import Data.List
import Debug.Trace

check t = check' [] [] t []

check' cs fs (Free x) d = True
check' cs fs (Bound i) d = True
check' cs fs (Lambda x t) d = check' cs fs t d
check' cs fs (Con c ts) d = all (\t -> check' cs fs t d) ts
check' cs fs (Apply t u) d = check' cs fs t d
check' cs fs (Call f ts) d = case lookup f d of
                                Nothing -> error ("Undefined function: "++f)
                                Just (xs,t) -> if f `elem` fs
                                               then not (null (xs `intersect` cs))
                                               else check' cs (f:fs) t d
check' cs fs (Case t bs) d = let cs' = case t of
                                          Free x -> x:cs
                                          _ -> cs
                             in all (\(c,xs,t) -> check' cs' fs t d) bs
check' cs fs (Let x t u) d = check' cs fs t d && check' cs fs u d
check' cs fs (Letrec f xs t u) d = let f' = rename (fst (unzip d)) f
                                       t' = foldr concrete (renameFun f f' t) xs
                                       u' = renameFun f f' u
                                   in  check' cs fs u' ((f',(xs,t')):d)

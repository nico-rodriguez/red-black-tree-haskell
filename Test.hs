module Test where

import RBT

t0 :: RBT Int
t0 = insert (Root E) 3

t1 :: RBT Int
t1 = insert t0 1

t2 :: RBT Int
t2 = insert t1 2

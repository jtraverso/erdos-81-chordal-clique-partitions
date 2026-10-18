# Author: Juan Pablo Traverso Gianini
from certo import Spec
from z3 import Reals, Real, Ints, And

def spec():
    W,L,U,g,h,r,t = Reals("W L U g h r t")
    s = Spec()
    s.assume('dual', W <= U)
    s.assume('first', g >= L-r)
    s.assume('second', h >= g-t)
    s.assume('feasible', h <= W)
    s.claim(And(W-h >= 0,W-h <= U-L+r+t))
    return s

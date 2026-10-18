# Author: Juan Pablo Traverso Gianini
from certo import Spec
from z3 import Reals, Real, Ints, And

def spec():
    W,L,U,g,r = Reals("W L U g r")
    s = Spec()
    s.assume('dual_upper', W <= U)
    s.assume('realization_lower', L-r <= g)
    s.assume('feasible_gain', g <= W)
    s.claim(And(0 <= W-g, W-g <= U-L+r-1))
    return s

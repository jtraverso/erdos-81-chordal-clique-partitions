# Author: Juan Pablo Traverso Gianini
from certo import Spec
from z3 import Reals, Real, Ints, And

def spec():
    nu,R = Ints("nu R"); U = Real("U")
    s = Spec()
    s.assume('feasible', R <= nu)
    s.assume('dual', nu <= U)
    s.assume('stop', U < R+1)
    s.claim(nu == R)
    return s

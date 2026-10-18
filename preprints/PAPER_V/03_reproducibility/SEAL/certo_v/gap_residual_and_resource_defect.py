# Author: Juan Pablo Traverso Gianini
from certo import Spec
from z3 import Reals, Real, Ints, And

def spec():
    relax,nu,cover,epsilon = Reals("relax nu cover epsilon")
    s = Spec()
    s.assume('feasible_pairs', nu <= cover)
    s.assume('resource_excess', relax-cover <= epsilon)
    s.assume('relaxation', nu <= relax)
    s.claim(And(0 <= relax-nu, relax-nu <= cover-nu+epsilon))
    return s

# Author: Juan Pablo Traverso Gianini
from certo import Spec
from z3 import Reals, Real, Ints, And

def spec():
    nu,relax,cover = Reals("nu relax cover")
    s = Spec()
    s.assume('all_scheduled', nu == cover)
    s.assume('upper_relaxation', relax >= nu)
    s.assume('positive', nu >= 0)
    s.claim(relax == nu)
    return s

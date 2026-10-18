# Author: Juan Pablo Traverso Gianini
from certo import Spec
from z3 import Reals, Real, Ints, And

def spec():
    initial,final,steps,cover = Ints("initial final steps cover")
    s = Spec()
    s.assume('start', initial >= 0)
    s.assume('improvement', final >= initial+steps)
    s.assume('capacity', final <= cover)
    s.claim(steps <= cover-initial)
    return s

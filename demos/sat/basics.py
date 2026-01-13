
"""
Basics of using the Z3 Python interface for propositional SAT
"""

from z3 import *

p = Bool('p')
q = Bool('q')
r = Bool('r')

f1 = Implies(p, q)
f2 = r == Not(q)
f3 = Or(Not(p), r)

s = Solver()
s.add(f1)
s.add(f2)
s.add(f2)
print((s.check()))
m = s.model()
print(m)
print((m[p]))

p = Bool('p')
q = Bool('q')
print((And(p, q, True)))
print((simplify(And(p, q, True))))
print((simplify(And(p, False))))

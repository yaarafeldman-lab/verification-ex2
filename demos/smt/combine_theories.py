from z3 import *

x, y = Consts('x y', IntSort())  # Integer constants
A    = DeclareSort('A')  # An uninterpreted sort A
a, b = Consts('a b', A)  # Constants of sort A

f = Function('f', IntSort(), A)  # f: Int -> A
g = Function('g', A, IntSort())  # g: A -> Int
P = Function('P', A, BoolSort())  # P: A -> Bool


print("Example 1:")
s = Solver()
s.add((y * g(f(y))) < 0)
s.add((5 + g(f(5))) % 2 == 0)
print(s)
print(s.check())
print(s.model())
print()

print("Example 2:")
s = Solver()
s.add(ForAll([x], Implies(x > 0, P(f(x)))))
s.add(ForAll([x], Implies(x < 0, Not(P(f(x))))))
s.add(ForAll([a], Implies(P(a), g(a) < 0)))
s.add(ForAll([a], Implies(Not(P(a)), g(a) > 0)))
print(s)
print(s.check())
print(s.model())


print("Example 3:")
s = Solver()
s.add(ForAll([x], Implies(x % 2 == 0, P(f(x)))))
s.add(ForAll([x], Implies(x % 2 == 1, Not(P(f(x))))))
s.add(ForAll([a], Implies(P(a), g(a) % 2 == 1)))
s.add(ForAll([a], Implies(Not(P(a)), g(a) % 2 == 0)))
s.add((x + g(f(x))) % 2 == 0)
s.add((1 + g(f(1))) % 2 == 0)
s.add(g(f(1)) == 1)
print(s)
print(s.check())
print()


print("Example 4 (will time out after 5 seconds):")
s = Solver()
s.set(timeout=5000)
s.add(ForAll([x], g(f(x)) > x))
print(s.check())

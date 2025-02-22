from z3 import *
from pro_print import *

# Z3 is an SMT solver. In this lecture, we'll discuss
# the basis usage of Z3 through some working example, the
# primary goal is to introduce how to use Z3 to solve
# the satisfiability problems we've discussed in the past
# several lectures.
# We must emphasize that Z3 is just one of the many such SMT
# solvers, and by introducing Z3, we hope you will have a
# general understanding of what such solvers look like, and
# what they can do.

########################################
# Basic propositional logic

# In Z3, we can declare two propositions just as booleans, this
# is rather natural, for propositions can have values true or false.
# To declare two propositions P and Q:
P = Bool('P')
Q = Bool('Q')
# or, we can use a more compact shorthand:
P, Q = Bools('P Q')


# We can build propositions by writing Lisp-style abstract
# syntax trees, for example, the disjunction:
# P \/ Q
# can be encoded as the following AST:
F = Or(P, Q)
# Output is : Or(P, Q)
print(F)

# Note that the connective '\/' is called 'Or' in Z3, we'll see
# several other in the next.

# We have designed the function 'pretty_print(expr)' for you,
# As long as we input the expression defined by z3, we can output
# propositions that are suitable for us to read.
# Here‘s an example:

P, Q = Bools('P Q')
F = Or(P, Q)

# Output is : P \/ Q
pretty_print(F)

################################################################
##                           Part A                           ##
################################################################

# exercises 1 : P -> (Q -> P)
# Please use z3 to define the proposition.
# Note that you need to define the proposition, and prove it.
P, Q = Bools('P Q')
F = Implies(Q, P)
G = Implies(P, F)
pretty_print(G)
solver = Solver()
solver.add(Not(G))
assert solver.check() == unsat
# raise NotImplementedError()


# exercise 2 : (P -> Q) -> ((Q -> R) -> (P -> R))
# Please use z3 to define the proposition.
# Note that you need to define the proposition, and prove it.
p, q, r = Bools('p q r')
f = Implies(Implies(p, q), Implies(Implies(q, r), Implies(p, r)))
solver = Solver()
pretty_print(f)
solver.add(Not(f))
assert solver.check() == unsat
# # raise NotImplementedError('TODO: Your code here!')

# exercise 3 : (P /\ (Q /\ R)) -> ((P /\ Q) /\ R)
# Please use z3 to define the proposition.
# Note that you need to define the proposition, and prove it.
p, q, r = Bools('p q r')
solver = Solver()
f = Implies(And(p, And(q, r)), And(And(p, q), r))
pretty_print(f)
solver.add(Not(f))
assert solver.check() == unsat
# raise NotImplementedError('TODO: Your code here!')

# exercise 4 : (P \/ (Q \/ R)) -> ((P \/ Q) \/ R)
# Please use z3 to define the proposition.
# Note that you need to define the proposition, and prove it.
solver = Solver()
f4 = Implies(Or(p, Or(q, r)), Or(Or(p, q), r))
pretty_print(f4)
solver.add(Not(f4))
assert solver.check() == unsat
# raise NotImplementedError('TODO: Your code here!')

# exercise 5 : ((P -> R) /\ (Q -> R)) -> ((P /\ Q) -> R)
# Please use z3 to define the proposition.
# Note that you need to define the proposition, and prove it.
# Note that you need to define the proposition, and prove it.
solver = Solver()
f5 = Implies(And(Implies(p,  r), Implies(q, r)), Implies(And(p, q), r))
pretty_print(f5)
solver.add(Not(f5))
assert solver.check() == unsat
# raise NotImplementedError('TODO: Your code here!')

# exercise 6 : ((P /\ Q) -> R) <-> (P -> (Q -> R))
# Please use z3 to define the proposition.
# Note that you need to define the proposition, and prove it.
solver = Solver()
f6l = Implies(And(p, q), r)
f6r = Implies(p, Implies(q, r))
f6 = (f6l == f6r)
# f6 = Implies(And(Implies(p,  r), Implies(q, r)), Implies(And(p, q), r))
pretty_print(f6)
solver.add(Not(f6))
assert solver.check() == unsat
# raise NotImplementedError('TODO: Your code here!')

# exercise 7 : (P -> Q) -> (¬Q -> ¬P)
# Please use z3 to define the proposition
# Note that you need to define the proposition, and prove it.
solver = Solver()
f7 = Implies((Implies(p,  q)), Implies(Not(q), Not(p)))
pretty_print(f7)
solver.add(Not(f7))
assert solver.check() == unsat
# raise NotImplementedError('TODO: Your code here!')


################################################################
##                           Part B                           ##
################################################################

# Before writing the src first, we need to understand the
# quantifier. ∀ x.P (x) means that for any x, P (x) holds,
# so both x and P should be a sort types. IntSort() and BoolSort()
# are given in Z3
# IntSort(): Return the integer sort in the given context.
# BoolSort(): Return the Boolean Z3 sort.
isort = IntSort()
bsort = BoolSort()

# Declare a Int variable x
x = Int('x')

# Declare a function P with input of isort type and output
# of bsort type
P = Function('P', isort, bsort)

# It means ∃x.P(x)
F = Exists(x, P(x))
print(F)
pretty_print(F)

# Now you can complete the following exercise based on the example above

# exercise 8 : # ∀x.(¬P(x) /\ Q(x)) -> ∀x.(P(x) -> Q(x))
# Please use z3 to define the proposition.
# Note that you need to define the proposition, and prove it.
p = Function('p', isort, bsort)
q = Function('q', isort, bsort)
f8l = ForAll(x, And(Not(p(x)), q(x)))
f8r = ForAll(x, Implies(p(x), q(x)))
f8 = Implies(f8l, f8r)
pretty_print(f8)
solver = Solver()
solver.add(Not(f8))
assert solver.check() == unsat
# raise NotImplementedError('TODO: Your code here!')

# exercise 9 : ∀x.(P(x) /\ Q(x)) <-> (∀x.P(x) /\ ∀x.Q(x))
# Please use z3 to define the proposition.
# Note that you need to define the proposition, and prove it.
# raise NotImplementedError('TODO: Your code here!')
p, q = Function('p', isort, bsort), Function('q', isort, bsort)
f = (ForAll(x, And(p(x), q(x))) == And(ForAll(x, p(x)), ForAll(x, q(x))))
pretty_print(f)
solver = Solver()
solver.add(Not(f))
assert solver.check() == unsat

# exercise 10 : ∃x.(¬P(x) \/ Q(x)) -> ∃x.(¬(P(x) /\ ¬Q(x)))
# Please use z3 to define the proposition.
# Note that you need to define the proposition, and prove it.
# raise NotImplementedError('TODO: Your code here!')
f10 = Implies(Exists(x, Or(Not(p(x)), q(x))),
              Exists(x, Not(And(p(x), Not(q(x))))))
pretty_print(f10)
solver = Solver()
solver.add(Not(f10))
assert solver.check() == unsat

# exercise 11 : ∃x.(P(x) \/ Q(x)) <-> (∃x.P(x) \/ ∃x.Q(x))
# Please use z3 to define the proposition.
# Note that you need to define the proposition, and prove it.
# raise NotImplementedError('TODO: Your code here!')

# exercise 12 : ∀x.(P(x) -> ¬Q(x)) -> ¬(∃x.(P(x) /\ Q(x)))
# Please use z3 to define the proposition.
# Note that you need to define the proposition, and prove it.
# raise NotImplementedError('TODO: Your code here!')

# exercise 13 : ∃x.(P(x) /\ Q(x)) /\ ∀x.(P(x) -> R(x)) -> ∃x.(R(x) /\ Q(x))
# Please use z3 to define the proposition.
# Note that you need to define the proposition, and prove it.
# raise NotImplementedError('TODO: Your code here!')

# exercise 14 : ∃x.∃y.P(x, y) -> ∃y.∃x.P(x, y)
# Please use z3 to define the proposition.
# Note that you need to define the proposition, and prove it.
# raise NotImplementedError('TODO: Your code here!')
y = Int('y')
p=Function('p',isort,isort,bsort)
f14 = Implies(Exists([x, y], p([x, y])), Exists([y, x], p([x, y])))
pretty_print(f14)
solver = Solver()
solver.add(Not(f14))
assert solver.check() == unsat
# exercise 15 : P(b) /\ (∀x.∀y.(P(x) /\ P(y) -> x = y)) -> (∀x.(P(x) <-> x = b))
# Please use z3 to define the proposition.
# Note that you need to define the proposition, and prove it.
# raise NotImplementedError('TODO: Your code here!')
p=Function('p',isort,bsort)
b=Int('b')
f15l=And(p(b),ForAll([x,y],Implies(And(p(x),p(y)),(x==y))))
f15r=ForAll(x,(p(x)==(x==b)))
f15=Implies(f15l,f15r)
pretty_print(f15)
solver = Solver()
solver.add(Not(f15))
assert solver.check() == unsat

################################################################
##                           Part C                           ##
################################################################

# Challenge:
# We provide the following two rules :
#     ----------------(odd_1)
#           odd 1
#
#           odd n
#     ----------------(odd_ss)
#         odd n + 2
#
# Please prove that integers 9, 25, and 99 are odd numbers.

# declare sorts: isort and bsort
isort = IntSort()
bsort = BoolSort()
solver=Solver()
isodd=Function('f',isort,bsort)
p=isodd(1)
q=ForAll(x,Implies(isodd(x),isodd(x+2)))
pretty_print(p)
pretty_print(q)
solver.add(p)
solver.add(q)
solver.add(isodd(9))
solver.add(isodd(25))
solver.add(isodd(99))
assert solver.check()==sat

# raise NotImplementedError('TODO: Your code here!')
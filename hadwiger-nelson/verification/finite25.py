#!/usr/bin/env python3
"""Exact finite-table part of the F_25 unit-quadrance chromatic computation."""
from collections import Counter
from fractions import Fraction as Q
from itertools import product

V = list(product(range(5), repeat=4))
S = [v for v in V if (v[0]**2 + 3*v[1]**2 + v[2]**2 + 3*v[3]**2) % 5 == 1
     and (v[0]*v[1]+v[2]*v[3]) % 5 == 0]
assert len(S) == 24
assert all((x+u+2*v)%5 != 0 for x,y,u,v in S)
distribution = Counter()
for a in V:
    if not any(a): continue
    count = Counter(sum(x*y for x,y in zip(a,v))%5 for v in S)
    assert count[1] == count[4] and count[2] == count[3]
    distribution[(count[0],count[1],count[2])] += 1
# λ=(2n0-n1-n2 + (n1-n2)√5)/2; use 2 < √5 < 9/4,
# taking the appropriate endpoint depending on the sign.
def lower(t):
    n0,n1,n2=t
    return Q(2*n0-n1-n2,2) + Q(n1-n2,2)*(2 if n1>=n2 else Q(9,4))
assert len(V) == 625 and sum(distribution.values()) == 624
L = min(map(lower, distribution))
assert L == Q(-31,4)
# For a d-regular graph with all nontrivial eigenvalues >= L,
# Hoffman gives alpha <= N*(-L)/(d-L).
alpha_upper = len(V)*(-L)/(len(S)-L)
assert alpha_upper < Q(len(V),4)
for t,num in sorted(distribution.items()):
    print(*t,num)
print(f'least certified lower bound {L}, independence number at most {alpha_upper.numerator//alpha_upper.denominator}')
print('chromatic number 5')

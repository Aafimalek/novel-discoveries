"""Exact check of the key inequality behind Var S <= E S, for arbitrary prime sets.

For a finite set P of primes, Q = prod P, N1 = prod (q - 1), and an interval I of
L consecutive integers, the claim is
  sum_{j != j' in I} prod_{q in P} (q - nu_q(j - j')) <= L (L - 1) N1^2 / Q,
where nu_q(d) = 1 if q | d and 2 otherwise. Also checks Var S <= E S by
enumerating Omega = prod_q Z/q when it is small.
"""
import itertools
import random
from fractions import Fraction
from math import prod

PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43]
random.seed(1)
worst = Fraction(0)
for trial in range(400):
    P = sorted(random.sample(PRIMES, random.randint(1, 7)))
    L = random.randint(1, 60)
    a = random.randint(-50, 50)
    I = range(a, a + L)
    Q, N1 = prod(P), prod(q - 1 for q in P)
    lhs = sum(prod(q - (1 if (j - k) % q == 0 else 2) for q in P)
              for j in I for k in I if j != k)
    rhs = Fraction(L * (L - 1) * N1 * N1, Q)
    assert lhs <= rhs, (P, L, a, lhs, rhs)
    if rhs:
        worst = max(worst, lhs / rhs)
print("pair-sum inequality holds in 400 random cases; max lhs/rhs =", float(worst))

for P in ([2, 3, 5], [2, 3, 5, 7], [3, 5, 7], [2, 5, 11], [2, 3, 5, 7, 11]):
    for L in (1, 2, 5, 9, 14):
        I = range(3, 3 + L)
        omegas = itertools.product(*[range(q) for q in P])
        s1 = s2 = n = 0
        for w in omegas:
            s = sum(all(w[i] != j % q for i, q in enumerate(P)) for j in I)
            s1 += s; s2 += s * s; n += 1
        mean = Fraction(s1, n); var = Fraction(s2, n) - mean * mean
        assert var <= mean, (P, L, var, mean)
print("Var S <= E S verified by enumeration for all listed cases")

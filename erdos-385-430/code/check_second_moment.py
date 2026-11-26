"""Brute-force check of the second-moment computation in Theorem A.

For small J and T, enumerate every residue n mod Q = (product of primes <= z),
z = 2J + T, and compare E[S], E[S^2] and P(S = 0) with the formulas
E[S] = (J+1) V and E[S^2] = (J+1) V + V^2 sum_{j != j'} S_z(j - j').
"""
from fractions import Fraction
from math import gcd, prod


def primes_upto(z):
    return [p for p in range(2, z + 1) if all(p % q for q in range(2, int(p**0.5) + 1))]


def singular_series_z(d, ps):
    value = Fraction(1)
    for q in ps:
        nu = 1 if d % q == 0 else 2
        value *= Fraction(q - nu, q) / Fraction(q - 1, q) ** 2
    return value


for J, T in [(1, 1), (2, 1), (2, 3), (3, 2), (4, 1), (5, 1), (6, 1), (6, 3), (7, 1)]:
    z = 2 * J + T
    ps = primes_upto(z)
    Q = prod(ps)
    if Q > 600000:
        continue
    js = range(J, 2 * J + 1)
    s1 = s2 = zero = 0
    for n in range(Q):
        s = sum(1 for j in js if gcd(n - j, Q) == 1)
        s1 += s
        s2 += s * s
        zero += s == 0
    V = prod(Fraction(q - 1, q) for q in ps)
    e1 = (J + 1) * V
    e2 = e1 + V * V * sum(singular_series_z(j - k, ps) for j in js for k in js if j != k)
    var = e2 - e1 * e1
    ok = Fraction(s1, Q) == e1 and Fraction(s2, Q) == e2
    print(f"J={J} T={T} z={z} Q={Q}: formulas {'match' if ok else 'MISMATCH'}; "
          f"P(S=0)={zero / Q:.4f} <= Var/E^2={float(var / e1**2):.4f}; Var/E={float(var / e1):.3f}")

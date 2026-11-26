"""Check single values of n against the Erdos #430 definition by direct factoring.

For each n, list every m with 1 < m < n whose prime factors all exceed n - m,
and report whether all of them are prime. Uses trial division only.
"""
import sys


def prime_factors(m):
    out, d = [], 2
    while d * d <= m:
        if m % d == 0:
            out.append(d)
            while m % d == 0:
                m //= d
        d += 1 if d == 2 else 2
    if m > 1:
        out.append(m)
    return out


def terms(n):
    # Composite m with all prime factors > n - m satisfy n - m < sqrt(n),
    # and a prime m qualifies exactly when m > n - m. Scan every m anyway.
    found = []
    for m in range(n - 1, 1, -1):
        if all(p > n - m for p in prime_factors(m)):
            found.append(m)
    return found


for n in map(int, sys.argv[1:]):
    t = terms(n)
    composite = [m for m in t if len(prime_factors(m)) > 1 or prime_factors(m)[0] != m]
    print(n, "terms:", len(t), "first:", t[:6], "composite terms:", composite[:5],
          "ALL PRIME" if not composite else "has composite term")

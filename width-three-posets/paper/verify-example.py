"""Exact ideal-DP check of the family in the example (not a Lean proof)."""

from functools import cache
from math import comb
from sys import argv


def counts(m, comparison=None):
    a, b, x, X, y, Y, Z = range(7)
    u = tuple(range(7, 7 + m))
    v = tuple(range(7 + m, 8 + 2*m))
    n = 8 + 2*m
    incoming = [0] * n
    edges = [(b, x), (x, X), (b, y), (y, Y), (Y, Z)]
    for chain in (u, v):
        edges.extend((p, chain[0]) for p in (a, X, Y))
        edges.extend(zip(chain, chain[1:]))
    if comparison:
        edges.append(comparison)
    for p, q in edges:
        incoming[q] |= 1 << p

    @cache
    def rec(ideal):
        if ideal == (1 << n) - 1:
            return 1
        return sum(
            rec(ideal | (1 << i))
            for i, need in enumerate(incoming)
            if not ideal & (1 << i) and ideal & need == need
        )

    return rec(0)


for m in range(1, 1 + (int(argv[1]) if len(argv) > 1 else 25)):
    k = 2*m + 1
    c = comb(k, m)
    total = counts(m)
    assert total == (36*k + 70) * c
    assert counts(m, (0, 1)) == (6*k + 10) * c
    xy = counts(m, (2, 4))
    assert xy == (18*k + 28) * c
    assert total <= 3*xy <= 2*total
    assert 6*counts(m, (0, 1)) < total
print(f"Exact total and comparison counts checked for m=1 through {m}.")

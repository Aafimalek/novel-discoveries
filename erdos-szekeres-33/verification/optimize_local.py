#!/usr/bin/env python3
"""Exact minimization of local signotope+parity CNF by finite set cover."""
from itertools import product
from functools import cache

ROWS = list(product((False, True), repeat=5))


def good(row):
    a, b, c, d, q = row
    return (a <= b <= c <= d or a >= b >= c >= d) and (q == a ^ b ^ c ^ d)


G = tuple(r for r in ROWS if good(r))
B = tuple(r for r in ROWS if not good(r))


def matches(cube, r):
    return all(x == -1 or x == int(y) for x, y in zip(cube, r))


primes = []
for c in product((-1, 0, 1), repeat=5):
    if any(matches(c, g) for g in G):
        continue
    shrunk = tuple(c[:i]+(-1,)+c[i+1:] for i in range(5) if c[i] >= 0)
    if all(any(matches(p, g) for g in G) for p in shrunk):
        m = sum(1 << i for i, r in enumerate(B) if matches(c, r))
        primes.append((c, m, sum(x != -1 for x in c)))
by_bit = [[i for i, (_, m, _) in enumerate(primes) if (m >> b) & 1] for b in range(len(B))]


@cache
def best(mask):
    if not mask:
        return (0, 0, ())
    b = min((j for j in range(len(B)) if (mask >> j) & 1), key=lambda j: len(by_bit[j]))
    res = (len(B) + 1, 0, ())
    for i in by_bit[b]:
        _, covered, length = primes[i]
        k, l, indices = best(mask & ~covered)
        res = min(res, (k + 1, l + length, (i, *indices)))
    return res


def main():
    k, l, indices = best((1 << len(B)) - 1)
    clauses = tuple(tuple(-(i+1) if x else i+1 for i, x in enumerate(primes[j][0]) if x != -1)
                    for j in indices)
    print(f"allowed={len(G)} forbidden={len(B)} prime implicates={len(primes)}")
    print(f"minimal local clauses={k}, literals={l}; state count={best.cache_info().currsize}")
    print(clauses)
    for item in ROWS:
        assert good(item) == all(any(item[abs(v)-1] == (v > 0) for v in c) for c in clauses)


if __name__ == "__main__":
    main()

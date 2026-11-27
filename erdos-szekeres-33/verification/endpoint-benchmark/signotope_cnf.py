#!/usr/bin/env python3
"""Compact sorted-orientation relaxation of planar Erdős–Szekeres.

Run: python3 signotope_cnf.py 9 5 es9-k5.cnf
A SAT model is a sign assignment, NOT necessarily a real point set.
An UNSAT trace still needs an independent checker and a checked DIMACS link.
"""
from argparse import ArgumentParser
from itertools import combinations, product
from math import comb

BITS4 = list(product((False, True), repeat=4))
# Each triple uses signed local slots 1..4 for orientation bits and 5 for parity.
# Exact truth table is checked in LocalCNF.lean.
COMPACT = ((1, 4, -5), (3, -4, 5), (2, -3, -5), (1, -2, 5),
           (-1, 2, 5), (-2, 3, -5), (-3, 4, 5), (-1, -4, -5))


def monotone(row):
    return tuple(sorted(row)) == row or tuple(sorted(row, reverse=True)) == row


def forbidden(ids, bits):
    """A clause falsified exactly on bits for ids."""
    return tuple(-i if bit else i for i, bit in zip(ids, bits, strict=True))


def generate(n, k, path, baseline=False):
    base = comb(n, 3)
    total = base + comb(n, 4)
    expected = comb(n, 4) * (24 if baseline else len(COMPACT)) + comb(n, k)
    triple = {abc: j for j, abc in enumerate(combinations(range(n), 3), 1)}
    quad = {abcd: j for j, abcd in enumerate(combinations(range(n), 4), 1 + base)}
    pattern4 = tuple(r for r in BITS4 if not monotone(r))
    assert len(pattern4) == 8
    seen = 0
    with open(path, "w", encoding="ascii", buffering=1 << 20) as cnf:
        print(f"p cnf {total} {expected}", file=cnf)

        def put(lits):
            nonlocal seen
            seen += 1
            print(" ".join(map(str, lits)), "0", file=cnf)

        for abcd, q in quad.items():
            xs = tuple(triple[abc] for abc in combinations(abcd, 3))
            ids = (*xs, q)
            if baseline:
                for r in pattern4:
                    put(forbidden(xs, r))
                for r in BITS4:
                    odd = bool(sum(r) % 2)
                    put(forbidden(ids, (*r, not odd)))
            else:
                for c in COMPACT:
                    put(tuple(ids[v-1] if v > 0 else -ids[-v-1] for v in c))
        for S in combinations(range(n), k):
            put(tuple(quad[abcd] for abcd in combinations(S, 4)))
    assert seen == expected
    return total, seen


def main():
    p = ArgumentParser(description=__doc__)
    p.add_argument("n", type=int)
    p.add_argument("k", type=int)
    p.add_argument("output")
    p.add_argument("--baseline", action="store_true", help="emit separate packet and parity clauses")
    a = p.parse_args()
    if not 4 <= a.k <= a.n:
        p.error("require 4 <= k <= n")
    print(generate(a.n, a.k, a.output, a.baseline))


if __name__ == "__main__":
    main()

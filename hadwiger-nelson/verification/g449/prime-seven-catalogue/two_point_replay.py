#!/usr/bin/env python3
"""G449 arbitrary two-point extension: exact, bounded-memory certificate replay.

Put this file alongside audit_layers.py, or add that directory to PYTHONPATH.
No solver or floating-point arithmetic is used; NumPy evaluates fixed-modulus
integer polynomials in one first-vertex shard at a time.
"""
from argparse import ArgumentParser
from collections import Counter
from hashlib import sha256
from itertools import combinations
from math import comb
from pathlib import Path
import json

import numpy as np

from audit_layers import (PHI, PINNED, catalogue, norm_numerator,
                          parse_sparse6, root_multiplicity_mod7, sub)

GENERATOR = (-8, -6, 5, 5, 5, -3, -2, 4, 7, 1, -2, -4)
PRIMES = (43, 127, 211, 337, 379, 463, 547)
UNIT = (49,) + (0,) * 11
FULL_MASK = 31


def load_data(source, catalogue_path):
    raw = {k: (source / k).read_bytes() for k in PINNED}
    assert {k: sha256(b).hexdigest() for k, b in raw.items()} == PINNED
    hdr, *rows = raw["G449.k21"].decode("ascii").splitlines()
    assert hdr.split() == ["K21", "42", "12", "49", "449"]
    rows = [tuple(map(int, line.split())) for line in rows if line.strip()]
    assert all(len(r) == 13 and all(a % 7 == 0 for a in r[:-1]) for r in rows)
    pts = [tuple(a // 7 for a in r[:-1]) for r in rows]
    orig = tuple(r[-1] for r in rows)
    n, edges = parse_sparse6(raw["G449.s6"])
    assert n == len(pts) == len(set(pts)) == 449 and len(edges) == 2198

    # Completeness uses the pole classification in the accompanying paper.
    # Verify the exact seed, its first pole, and every supplied catalogue row.
    assert norm_numerator(GENERATOR) == UNIT
    assert tuple(root_multiplicity_mod7(GENERATOR, r) for r in (3, 5)) == (5, 6)
    hdr, *rows = catalogue_path.read_text().splitlines()
    assert hdr.split() == ["n", "denominator"] + [f"a{i}" for i in range(12)]
    supplied = [tuple(map(int, line.split())) for line in rows if line.strip()]
    assert len(supplied) == 273 and all(len(r) == 14 and r[1] in (1, 7) for r in supplied)
    assert sorted(supplied) == sorted(catalogue(GENERATOR, 6))
    dirs = {tuple(sign * (7 // r[1]) * a for a in r[2:])
            for r in supplied for sign in (-1, 1)}
    assert len(dirs) == 546 and all(norm_numerator(v) == UNIT for v in dirs)

    recomputed_edges = {(i, j) for i, j in combinations(range(n), 2)
                        if sub(pts[i], pts[j]) in dirs}
    assert recomputed_edges == edges
    print(f"Pinned inputs: {n} distinct base vertices, {len(edges)} exact induced edges;",
          f"{len(dirs)} signed unit steps regenerated; {comb(n,2):,} base pair checks.",
          flush=True)
    return pts, orig, edges, dirs


def checked_colourings(orig, edges, witness_path):
    data = json.loads(witness_path.read_text())
    witnesses = {}
    cols = [orig]
    for row in data["single"]:
        x = tuple(row["point"])
        assert len(x) == 12 and x not in witnesses
        c = tuple(map(int, row["colors"]))
        assert len(c) == 450 and set(c) == set(range(5))
        cols.append(c[:449])
        witnesses[x] = (row["neighbors"], c)
    assert len(cols) == 35 and len(witnesses) == 34
    for c in cols:
        assert len(c) == 449 and set(c) == set(range(5))
        assert all(c[i] != c[j] for i, j in edges)
    return cols, witnesses


def grid_neighbours(pts, dirs):
    # Packed bytes are an exact, injective encoding, not modular coordinates.
    # Assert widened sum range before pairing. For these pinned inputs every
    # sum fits one shifted unsigned byte per coefficient.
    assert max(abs(x) for a in pts for x in a) + max(abs(x) for d in dirs for x in d) < 128
    old = {bytes(a + 128 for a in x) for x in pts}
    centers = {}
    for i, x in enumerate(pts):
        base = tuple(a + 128 for a in x)
        for d in dirs:
            y = bytes(a + b for a, b in zip(base, d))
            prev = centers.get(y)
            if prev is None:
                centers[y] = i
            elif isinstance(prev, int):
                centers[y] = [prev, i]
            else:
                prev.append(i)
    hist = Counter(1 if isinstance(v, int) else len(v)
                   for k, v in centers.items() if k not in old)
    print(f"{sum(hist.values()):,} outside grid neighbours; outside degree histogram",
          dict(sorted(hist.items())), flush=True)
    assert sum(hist.values()) == 229_320
    return centers, old


def triple_key(i, j, k, n):
    return (i * n + j) * n + k


def grid_triples(centers, n):
    # Centers include all original vertices, since they may witness a triple.
    out = set()
    for ns in centers.values():
        if isinstance(ns, list) and len(ns) >= 3:
            out.update(triple_key(i, j, k, n) for i, j, k in combinations(ns, 3))
    assert len(out) == 97_650
    print(f"{len(out):,} distinct base triples have a grid center.", flush=True)
    return out


def residue_maps(pts, p):
    root = next(r for r in range(2, p) if pow(r, 42, p) == 1
                and all(pow(r, d, p) != 1 for d in (6, 14, 21)))
    inverse = pow(root, -1, p)
    def powers(r):
        a = tuple(pow(r, i, p) for i in range(13))
        assert sum(x*y for x,y in zip(a, PHI)) % p == 0
        return a
    def values(r):
        a = powers(r)
        return np.array([sum(x*y for x, y in zip(q, a)) % p for q in pts], dtype=np.int64)
    return values(root), values(inverse)


def check_all_triples(pts, known):
    n = len(pts)
    # Pairs j<k grouped by j; shard for i uses suffix with i<j.
    all_j, all_k = np.triu_indices(n, 1)
    residue = [(p, *residue_maps(pts, p)) for p in PRIMES]
    acc = [0] * (len(PRIMES)+1)
    for i in range(n - 2):
        lo = np.searchsorted(all_j, i+1)
        j, k = all_j[lo:], all_k[lo:]
        acc[0] += len(j)
        for s, (p, x, y) in enumerate(residue, 1):
            a, b, c, d = x[j]-x[i], y[j]-y[i], x[k]-x[i], y[k]-y[i]
            U, V, W, D = a*b%p, c*d%p, ((a-c)*(b-d))%p, (a*d-b*c)%p
            # Everything fits signed int64, e.g. products below 2**29.
            keep = (U*V*W + 49*D*D) % p == 0
            j, k = j[keep], k[keep]
            acc[s] += len(j)
        for b, c in zip(j.tolist(), k.tolist()):
            assert triple_key(i, b, c, n) in known, (i, b, c)
    assert acc[0] == comb(n, 3) == 14_985_824
    # All known triples also pass every filter by their explicit unit witnesses.
    assert acc[-1] == len(known)
    print(f"{acc[0]:,} unordered base triples; surviving after each filter:",
          dict(zip(PRIMES, acc[1:])), flush=True)
    print("Every final survivor has a checked grid center.", flush=True)


def absent(neighbours, colours):
    seen = 0
    for i in neighbours:
        seen |= 1 << colours[i]
    return FULL_MASK ^ seen


def can_colour_pair(ma, mb, edge):
    # With both lists nonempty, failure on an edge occurs iff the
    # union has only one colour. This is true iff both are that singleton.
    u = ma | mb
    return bool(ma and mb and (not edge or (u & (u - 1))))


def check_grid_pairs(centers, old, dirs, cols, witnesses):
    pts = []
    seen_witnesses = set()
    for packed, ns in centers.items():
        if not isinstance(ns, list) or len(ns) < 4 or packed in old:
            continue
        p = tuple(a - 128 for a in packed)
        mask = tuple(absent(ns, c) for c in cols)
        if not mask[0]:
            needed, vector = witnesses[p]
            assert ns == needed
            assert all(vector[i] != vector[449] for i in ns)
            seen_witnesses.add(p)
        pts.append((p, mask))
    assert len(pts) == 1_043 and seen_witnesses == set(witnesses)
    checks = residual = edge_conflicts = unresolved = 0
    for (p, a), (q, b) in combinations(pts, 2):
        is_edge = sub(p, q) in dirs
        checks += 1
        if can_colour_pair(a[0], b[0], is_edge):
            continue
        residual += 1
        edge_conflicts += bool(a[0] and b[0])
        if not any(can_colour_pair(x, y, is_edge) for x, y in zip(a[1:], b[1:])):
            unresolved += 1
            print("Uncovered pair", p, q, flush=True)
    assert (checks, residual, edge_conflicts, unresolved) == (543_403, 34_911, 44, 0)
    print(f"{len(pts):,} outside grid points of degree at least 4; {checks:,} pairs.",
          flush=True)
    print(f"Published coloring fails on {residual:,} pairs, including {edge_conflicts:,}",
          "adjacent pairs with two nonempty original lists. All pass the 35-coloring test.",
          flush=True)


def main():
    pa = ArgumentParser(description=__doc__)
    pa.add_argument("input", type=Path)
    pa.add_argument("catalogue", type=Path)
    pa.add_argument("witnesses", type=Path)
    args = pa.parse_args()
    pts, orig, edges, dirs = load_data(args.input, args.catalogue)
    cols, witnesses = checked_colourings(orig, edges, args.witnesses)
    centers, old = grid_neighbours(pts, dirs)
    check_all_triples(pts, grid_triples(centers, len(pts)))
    check_grid_pairs(centers, old, dirs, cols, witnesses)
    print("Verified the finite conditions for arbitrary two-point extension.")


if __name__ == "__main__":
    main()

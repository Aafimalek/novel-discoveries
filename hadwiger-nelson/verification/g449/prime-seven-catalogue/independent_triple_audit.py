"""Independent truth-table and exact geometric audit of the G449 triple witness."""
from argparse import ArgumentParser
from collections import Counter
from itertools import combinations, product
from pathlib import Path
import json

from check_grid_triples import vertex_flags, pair_ok, path_ok, triangle
from two_point_replay import load_data
from audit_layers import PHI, parse_sparse6, sub


def exact_norm(x):
    # Compute raw conjugate Laurent product then do monic long division.
    a = [0] * 42
    for i, p in enumerate(x):
        for j, q in enumerate(x):
            if p and q:
                a[(i-j) % 42] += p*q
    for k in range(len(a)-1, 11, -1):
        c = a[k]
        if c:
            for j, p in enumerate(PHI):
                a[k-12+j] -= c*p
    return tuple(a[:12])


def check_mask_tables():
    choices = [[c for c in range(5) if a >> c & 1] for a in range(32)]
    flags = [vertex_flags((a,)) for a in range(32)]
    for a, b in product(range(32), repeat=2):
        assert bool(pair_ok(flags[a], flags[b])) == any(x != y for x,y in product(choices[a],choices[b]))
    for a, b, c in product(range(32), repeat=3):
        p = t = False
        for x, y, z in product(choices[a], choices[b], choices[c]):
            p |= x != y and y != z
            t |= x != y and y != z and x != z
        assert bool(path_ok(flags[a], flags[b], flags[c])) == p
        assert triangle((a,), (b,), (c,)) == t
    print("Independently exhausted 1,024 pair and 32,768 path/triangle mask vectors.")


def verify_witness(points, old_edges, data):
    new_points = list(map(tuple, data["points"]))
    all_points = points + new_points
    n = len(all_points)
    assert n == len(set(all_points)) == 503
    col = data["colors"]
    assert len(col) == n and set(col) == set("01234")
    known = {}
    geom = set()
    unit = (49,) + (0,)*11
    for i, j in combinations(range(n), 2):
        d = sub(all_points[i], all_points[j])
        if d[0] > 0:  # A cheap deterministic normalization when a0 isn't 0.
            d = tuple(-a for a in d)
        result = known.get(d)
        if result is None:
            result = known[d] = exact_norm(d) == unit
        if result:
            assert col[i]!=col[j]
            geom.add((i,j))
    assert {e for e in geom if e[1]<449} == old_edges
    assert len(geom)==data["edges"]==2545
    triples = [tuple(tr) for tr in data["triples"]]
    assert len(triples)==len(set(triples))==60
    assert all(len(tr)==3 and list(tr)==sorted(set(tr)) for tr in triples)
    assert {x for tr in triples for x in tr}==set(range(n-449))
    shape = Counter(sum((i+449,j+449) in geom for i,j in combinations(tr, 2)) for tr in triples)
    assert shape == {0:21,1:38,2:1}
    print("Independent exact Laurent geometry: 126,253 pair comparisons;",
          "2,545 induced edges on 503 distinct points; all colorings and 60 triple shapes pass.")


def main():
    ap = ArgumentParser(description=__doc__)
    ap.add_argument("input", type=Path)
    ap.add_argument("catalogue", type=Path)
    ap.add_argument("residual_witness", type=Path)
    a = ap.parse_args()
    points, _, edges, _ = load_data(a.input, a.catalogue)
    check_mask_tables()
    verify_witness(points, edges, json.loads(a.residual_witness.read_text()))


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Exact G449 arithmetic and pairwise-residue audit; standard Python only."""
import argparse
from collections import Counter, defaultdict
from hashlib import sha256
from itertools import combinations, product
from math import comb, gcd
from pathlib import Path

PINNED = {
    "G449.k21": "58a45c4e653ff63e0218e1dec988e0a532905969dda3fc7bf84a3c83874a3848",
    "G449.s6": "0db89dfb231a2722cb54a5bc3ce9e27afc672e73bd1230c41e08845b449e1b21",
}


def parse_sparse6(raw):
    s = raw.strip().removeprefix(b">>sparse6<<")
    assert s[0] == ord(":")
    six = [b - 63 for b in s[1:]]
    assert all(0 <= x < 64 for x in six)
    if six[0] != 63:
        n, data = six[0], six[1:]
    else:
        assert six[1] != 63  # Only the 18-bit extended header is needed here.
        n, data = (six[1] << 12) | (six[2] << 6) | six[3], six[4:]
    width = max(1, (n - 1).bit_length())
    bits = "".join(f"{a:06b}" for a in data)
    pos, v, edges = 0, 0, set()
    while pos + width < len(bits):
        edge_bit, x = int(bits[pos]), int(bits[pos + 1:pos + 1 + width], 2)
        pos += 1 + width
        v += edge_bit
        if x >= n or v >= n:
            break  # Padding.
        if x > v:
            v = x
        else:
            assert x < v and (x, v) not in edges
            edges.add((x, v))
    return n, edges


def sub(a, b):
    return tuple(x - y for x, y in zip(a, b))


# Low-to-high coefficients of the monic cyclotomic polynomial Phi_42.
PHI = (1, 1, 0, -1, -1, 0, 1, 0, -1, -1, 0, 1, 1)
POWERS = [(1,) + (0,) * 11]
for _ in range(42):
    a = POWERS[-1]
    POWERS.append(tuple(old - a[-1]*c for old, c in zip((0,) + a[:-1], PHI)))
assert POWERS[42] == POWERS[0] and len(set(POWERS[:42])) == 42


def mul(a, b):
    ans = [0] * 12
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            for k, c in enumerate(POWERS[(i+j) % 42]):
                ans[k] += x*y*c
    return tuple(ans)


def conjugate(a):
    return tuple(sum(x * POWERS[-i % 42][k] for i, x in enumerate(a))
                 for k in range(12))


def canonical(a):
    return min(a, tuple(-x for x in a))


def catalogue(u, bound):
    """Rows (signed pole exponent, common denominator, 12 coefficients)."""
    rows = []
    seen = set()
    for n in range(-bound, bound+1):
        g = u if n >= 0 else conjugate(u)
        denom, p = 1, POWERS[0]
        for _ in range(abs(n)):
            denom *= 7
            p = mul(p, g)
            d = gcd(denom, *p)
            denom, p = denom//d, tuple(x//d for x in p)
        assert denom == 7 ** ((abs(n)+5)//6)
        for z in sorted({canonical(mul(p, root)) for root in POWERS[:42]}):
            assert (denom, z) not in seen and norm_numerator(z) == (denom**2,) + (0,)*11
            seen.add((denom, z))
            rows.append((n, denom, *z))
    assert len(rows) == 21*(2*bound+1)
    return rows


def norm_numerator(z):
    ans = [0] * 12
    for i, a in enumerate(z):
        for j, b in enumerate(z):
            for k, c in enumerate(POWERS[(i-j) % 42]):
                ans[k] += a*b*c
    return tuple(ans)


def root_multiplicity_mod7(z, root):
    """First nonzero coefficient of p(root + X) modulo 7."""
    return next((k for k in range(len(z))
                 if sum(a * comb(i, k) * pow(root, i-k, 7)
                        for i, a in enumerate(z) if i >= k) % 7), len(z))


def trace_mod7(z):
    return sum(a * (pow(3, j, 7) + pow(5, j, 7)) for j, a in enumerate(z)) % 7


def four_color(z):
    return trace_mod7(z) % 3 if trace_mod7(z) != 6 else 3


def three_color(z):
    return sum(a * (-1)**j * (1 if j % 7 < 5 else -1)
               for j, a in enumerate(z)) % 3


def enum_residue_graph():
    vertices = tuple(product(range(7), repeat=2))
    steps = {(a, b) for a, b in vertices if a * b % 7 == 1}
    u, v = (3, 5), (5, 3)
    assert (u[0]*v[1] - u[1]*v[0]) % 7 != 0
    assert steps == {tuple((i*x + j*y) % 7 for x, y in zip(u, v))
                     for i, j in ((1, 0), (0, 1), (1, 1), (-1, 0), (0, -1), (-1, -1))}
    colors = lambda z: 3 if sum(z) % 7 == 6 else (sum(z) % 7) % 3
    edges = {(min(x, y), max(x, y)) for x in vertices for a in steps
             for y in [tuple((r+s) % 7 for r, s in zip(x, a))]}
    assert len(edges) == 147
    assert all(colors(x) != colors(y) for x, y in edges)
    # Triangle propagation reduces any 3-coloring to a color sequence
    # on the 7-cycle with both distance-1 and distance-2 constraints.
    assert not any(all(c[i] != c[(i+1) % 7] and c[i] != c[(i+2) % 7]
                       for i in range(7)) for c in product(range(3), repeat=7))
    return len(vertices), len(edges)


def induced_edges(points, rows):
    index = {x: i for i, x in enumerate(points)}
    steps = {tuple(sign * v * (7//r[1]) for v in r[2:])
             for r in rows for sign in (-1, 1)}
    edges = set()
    for i, x in enumerate(points):
        for d in steps:
            y = tuple(a+b for a,b in zip(x,d))
            j = index.get(y)
            if j is not None and i < j:
                edges.add((i,j))
    return edges


def audit(directory, output=None, bound=1):
    raw = {name: (directory / name).read_bytes() for name in PINNED}
    assert {k: sha256(v).hexdigest() for k, v in raw.items()} == PINNED
    header, *lines = raw["G449.k21"].decode().splitlines()
    assert header.split() == ["K21", "42", "12", "49", "449"]
    records = [tuple(map(int, line.split())) for line in lines if line.strip()]
    assert all(len(row) == 13 for row in records)
    points = [a[:-1] for a in records]
    n, edges = parse_sparse6(raw["G449.s6"])
    assert n == len(points) == len(set(points)) == 449 and len(edges) == 2198
    div = gcd(49, *(v for row in points for v in row))
    assert div == 7
    points = [tuple(v // div for v in row) for row in points]
    cosets = defaultdict(list)
    for i, p in enumerate(points):
        cosets[tuple(a % 7 for a in p)].append(i)
    ordered = sorted(cosets.values(), key=lambda ids: (len(ids), ids[0]))
    layer = {v: k for k, ids in enumerate(ordered) for v in ids}
    integral_repr = [
        tuple(d // 7 for d in sub(p, points[ordered[layer[i]][0]]))
        for i, p in enumerate(points)
    ]
    by_layer = Counter()
    quot = Counter()
    directions = {True: set(), False: set()}
    intra = defaultdict(set)
    for a, b in edges:
        d = sub(points[a], points[b])
        integral = all(t % 7 == 0 for t in d)
        assert integral == (layer[a] == layer[b])
        directions[integral].add(min(d, tuple(-t for t in d)))
        if integral:
            by_layer[layer[a]] += 1
            intra[a].add(b)
            intra[b].add(a)
            assert four_color(integral_repr[a]) != four_color(integral_repr[b])
            assert three_color(integral_repr[a]) != three_color(integral_repr[b])
        else:
            quot[tuple(sorted((layer[a], layer[b])))] += 1
    triangles = Counter(layer[a] for a in intra for b, c in combinations(intra[a], 2)
                        if a < b < c and c in intra[b])
    sizes = [len(ids) for ids in ordered]
    assert sizes == [1, 49, 49, 56, 63, 70, 77, 84]
    assert len([p for p in points if all(t % 7 == 0 for t in p)]) == 1
    assert sum(by_layer.values()) == 1092 and sum(quot.values()) == 1106
    assert all(norm_numerator(z) == (49,) + (0,) * 11
               for direction_set in directions.values() for z in direction_set)
    canonical_root_directions = {
        min(z, tuple(-t for t in z)) for z in POWERS[:42]
    }
    assert {tuple(t // 7 for t in z) for z in directions[True]} == canonical_root_directions
    assert all(triangles[i] > 0 for i in range(1, 8))
    assert len(canonical_root_directions) == 21 and all(three_color(z) for z in POWERS[:42])
    multiplicities = Counter((root_multiplicity_mod7(z, 3),
                              root_multiplicity_mod7(z, 5)) for z in directions[False])
    assert dict(multiplicities) == {(6, 5): 21, (5, 6): 7}
    u = min(z for z in directions[False]
            if (root_multiplicity_mod7(z, 3), root_multiplicity_mod7(z, 5)) == (5, 6))
    first_pole = catalogue(u, 1)
    first_pole_directions = {(r[1], r[2:]) for r in first_pole}
    assert {(7, z) for z in directions[False]} <= first_pole_directions
    assert {(1, tuple(t//7 for t in z)) for z in directions[True]} <= first_pole_directions
    denominator7 = catalogue(u, 6)
    assert all(r[1] in (1, 7) for r in denominator7) and len(denominator7) == 273
    assert induced_edges(points, denominator7) == edges
    assert {row[-1] for row in records} == set(range(5))
    assert all(records[i][-1] != records[j][-1] for i,j in edges)
    if output is not None:
        rows = first_pole if bound == 1 else denominator7 if bound == 6 else catalogue(u, bound)
        output.write_text("n\tdenominator\t" + "\t".join(f"a{i}" for i in range(12)) + "\n" +
                          "".join("\t".join(map(str, r)) + "\n" for r in rows))
    assert (len(directions[True]), len(directions[False])) == (21, 28)
    assert set(quot) - set(combinations(range(1,8), 2)) in ({(0,1)}, {(0,2)})
    assert len(quot) == 22 and set(combinations(range(1,8), 2)) <= set(quot)
    print("reduced common coefficient denominator:", 49 // div)
    print("layer sizes:", sizes)
    print("internal edges per layer:", [by_layer[i] for i in range(8)])
    print("triangles per layer:", [triangles[i] for i in range(8)])
    print("edges: internal / cross-layer:", sum(by_layer.values()), sum(quot.values()))
    print("unoriented directions: integral / nonintegral:", *(len(directions[b]) for b in (True, False)))
    print("all directions have exact unit norm; integral ones are all 42 signed powers")
    print("generator numerator over 7 (pole at evaluation 3):", u)
    print("full first-order pole catalogue (unoriented):", len(first_pole))
    print("full denominator-dividing-7 catalogue (unoriented):", len(denominator7))
    print("induced edges on existing coordinates:", len(edges), "(exact sparse6 match; original five-coloring valid)")
    print("nonintegral numerator multiplicities at (3,5):", sorted(multiplicities.items()))
    print("singleton quotient edge:", next(pair for pair in quot if pair[0] == 0))
    print("residue graph vertices / edges:", *enum_residue_graph())


if __name__ == "__main__":
    p = argparse.ArgumentParser()
    p.add_argument("input_directory", type=Path, help="directory containing G449.k21 and G449.s6")
    p.add_argument("--catalogue", type=Path, help="optional output TSV")
    p.add_argument("--pole-bound", type=int, default=1)
    args = p.parse_args()
    if args.pole_bound < 0:
        p.error("--pole-bound must be nonnegative")
    audit(args.input_directory, args.catalogue, args.pole_bound)

"""Verify that the 24-site control escapes even the rotation-invariant mod-5 filter."""
import importlib.util
import json
from fractions import Fraction
from hashlib import sha256
from pathlib import Path
from sys import argv

fixture, graph = map(Path, argv[1:])
assert sha256(fixture.read_bytes()).hexdigest() == "dbfa98684962ca65a1dd5302f002b60999b4b1d7d58a4e753c018f3559592a5f"
spec = importlib.util.spec_from_file_location("exact_fixture", fixture)
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
g = json.loads(graph.read_text())
assert g["basis_squares"] == [-3, 33, -7]
P = [tuple(map(Fraction, p)) for p in g["coordinates"]]
E = g["unit_edges"]
assert len(P) == 24 and len(E) == 50
assert all(m.norm(m.sub(P[i], P[j])) == m.ONE for i,j in E)
seen = {0}
while True:
    nxt = seen | {v for i,j in E for u,v in ((i,j),(j,i)) if u in seen}
    if nxt == seen:
        break
    seen = nxt
assert len(seen) == len(P)
dirs = [(i,j,m.sub(P[i],P[j])) for i,j in E]
def integral(z):
    return all(x.denominator % 5 for x in z)
i,j,u = next(d for d in dirs if integral(d[2]))
k,l,v = next(d for d in dirs if not integral(d[2]))
assert not integral(m.mul(v, m.bar(u)))
print(f"Connected 24-point control: exact unit edges {i}-{j} and {k}-{l} have a nonintegral direction quotient.")

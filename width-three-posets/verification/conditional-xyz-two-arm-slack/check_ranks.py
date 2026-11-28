"""Exact, tiny rank sanity check for the crossed h=3, r=t=5 example."""
from itertools import combinations, combinations_with_replacement

h = 3
prefix = ("b", "c", "q")
x = tuple(f"x{i}" for i in range(5))
y = tuple(f"y{i}" for i in range(5))
cross = (("x0", "y1"), ("y0", "x2"))

ranks = []
for x_positions in combinations(range(10), 5):
    indices = set(x_positions)
    X, Y = iter(x), iter(y)
    order = prefix + tuple(next(X) if i in indices else next(Y)
                           for i in range(10))
    rank = {u: i for i, u in enumerate(order, start=1)}
    if all(rank[u] < rank[v] for u, v in cross):
        ranks.append(rank)

assert any(r["x1"] < r["y0"] for r in ranks)
assert any(r["y0"] < r["x1"] for r in ranks)
assert max(r["x0"] for r in ranks) <= 2*h
assert all(r["y0"] <= 2*r["x0"] for r in ranks)
assert all(2*min(r["x1"],r["y1"]) <= 3*r["x0"] for r in ranks)
low_seed = prefix + ("x0","y0")
for z in x[1:] + y[1:]:
    for u, v in combinations_with_replacement(low_seed, 2):
        assert any(r[z] > r[u] + r[v] for r in ranks), (z,u,v)
print(f"Checked {len(ranks)} induced orders for the crossed h=3 example.")
print("Neither arm beyond its gate can be reached by any pair of seed ranks.")
print("The conditional XYZ minimum-rank criterion does reach one of x1,y1.")

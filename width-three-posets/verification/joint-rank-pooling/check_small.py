"""Tiny exact closure/rank diagnostics; none of the proofs depend on enumeration."""
from itertools import combinations, combinations_with_replacement

for m in range(1, 8):
    x = [("x", i) for i in range(m)]
    y = [("y", i) for i in range(m)]
    V = x+y
    edge = set(zip(x,x[1:])) | set(zip(y,y[1:]))
    edge |= set(zip(x,y[1:])) | set(zip(y,x[2:]))
    # Floyd–Warshall on the exact generating edge set.
    for b in V:
        edge |= {(a,c) for a in V for c in V if (a,b) in edge and (b,c) in edge}
    assert all((u,u) not in edge for u in V)
    actual = set()
    for i in range(m):
        for j in range(m):
            assert ((x[i],y[j]) in edge) == (j >= i+1)
            assert ((y[j],x[i]) in edge) == (i >= j+2)
            if (x[i],y[j]) not in edge and (y[j],x[i]) not in edge:
                actual.add(frozenset((x[i],y[j])))
    alternating=[v for pair in zip(x,y) for v in pair]
    path={frozenset((u,v)) for u,v in zip(alternating,alternating[1:])}
    assert actual==path
print("Exact transitive-closure checks: m=1,...,7; incomparability graph is the alternating path.")

prefix = ["b","q"]
x = [f"x{i}" for i in range(4)]
y = [f"y{i}" for i in range(4)]
ranks = []
for subset in combinations(range(8),4):
    xpos=set(subset)
    X,Y=iter(x), iter(y)
    order=prefix+[next(X) if i in xpos else next(Y) for i in range(8)]
    rank={v:i for i,v in enumerate(order, start=1)}
    if rank["x0"]<rank["y1"] and rank["y0"]<rank["x2"]:
        ranks.append(rank)
assert max(r["x1"]+r["y1"] for r in ranks)==13
assert min(2*(r["x0"]+r["y0"]) for r in ranks)==14
assert all(any(r[z]>r[u]+r[v] for r in ranks)
           for z in ("x1","y1")
           for u,v in combinations_with_replacement(prefix+["x0","y0"],2))
print(f"Crossed 4+4: {len(ranks)} induced orders; no single-head rank-pool works from the seed; joint sum 13 <= 14.")

"""Exact arithmetic and finite closure/rank audits. No solver or dependencies."""
from itertools import combinations

checked = 0
for h in range(2, 13):
    K = h // 2
    cap_A = 2*h - 2
    cap_B = cap_A + (K + 2)//3
    for i in range(13):
        for j in range(13):
            s, m = min(i, j), max(i, j)
            delta = i-j
            Delta = abs(delta)
            M = max(s, Delta)
            T = 2*M - Delta
            assert max(2*h+i+j+s, 2*(h+m)) == 2*h+i+j+M
            assert 3*T - (i+j) == (
                4*(s-Delta) if s >= Delta else 2*(Delta-s))
            assert (T == 0) == (i == 0 and j == 0)
            assert 2*h-1+T > cap_A
            if i+j >= K:
                assert 2*h-1+T > cap_B
            D = (i+2*j) % 20
            e, d = min(D, (i*j) % 20), D
            assert max(e-delta, d+delta) <= D+Delta
            checked += 1
print(f"Exact integer identities and theorem bounds: {checked} small triples.")

for n in range(1, 7):
    x = tuple(("x", i) for i in range(n))
    y = tuple(("y", i) for i in range(n))
    V = x+y
    gen = set(zip(x, x[1:])) | set(zip(y, y[1:]))
    gen |= set(zip(x, y[2:])) | set(zip(y, x[2:]))
    full = set(gen)
    for b in V:
        full |= {(a, c) for a in V for c in V if (a,b) in full and (b,c) in full}
    assert all((v,v) not in full for v in V)
    adj = {v: set() for v in V}
    for i in range(n):
        for j in range(n):
            u, v = x[i], y[j]
            assert ((u,v) in full) == (j >= i+2)
            assert ((v,u) in full) == (i >= j+2)
            if (u,v) not in full and (v,u) not in full:
                assert abs(i-j) <= 1
                adj[u].add(v)
                adj[v].add(u)
            else:
                assert abs(i-j) > 1
    reached = {x[0]}
    for _ in V:
        reached |= set().union(*(adj[v] for v in reached))
    assert reached == set(V)
    degree = max(map(len, adj.values()))
    assert degree == min(n,3)
    heads = []
    for c in combinations(range(2*n), n):
        choose_x, X, Y = set(c), iter(x), iter(y)
        R = [next(X) if k in choose_x else next(Y) for k in range(2*n)]
        rank = dict(zip(R, range(3,2*n+3))) # two fixed prefix points
        if all(rank[u] < rank[v] for u,v in gen):
            heads.append((rank[x[0]],rank[y[0]]))
    assert set(heads) == ({(3,4),(4,3)} if n==1 else
                          {(3,4),(4,3),(3,5),(5,3)})
    assert max(a+b for a,b in heads) == (7 if n==1 else 8)
    print(f"n={n}: exact connected closure, max degree {degree}, {len(heads)} legal orders; head ranks {sorted(set(heads))}.")

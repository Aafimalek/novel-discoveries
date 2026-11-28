"""Small exact check of the scope example; the writeup proves all n >= 5."""
from itertools import combinations
from fractions import Fraction

n = 5
b, q, a, ap = "b", "q", "a", "ap"
x = tuple(f"x{i}" for i in range(n))
y = tuple(f"y{i}" for i in range(n))
S = (b, q) + x + y
V = S + (a, ap)
G = {(b,q), (q,x[0]), (q,y[0]), (a,ap), (b,ap)}
G |= set(zip(x, x[1:])) | set(zip(y, y[1:]))
G |= set(zip(x, y[2:])) | set(zip(y, x[2:]))
T = set(G)
for m in V:
    T |= {(u,v) for u in V for v in V if (u,m) in T and (m,v) in T}
assert all((u,u) not in T for u in V)
assert {z for z in V if (a,z) in T} == {ap}
assert {b} | {z for z in V if (b,z) in T and (a,z) not in T} == set(S)
assert {u for u in V if not any((z,u) in T for z in V)} == {a,b}
assert {u for u in V if not any((u,z) in T for z in V)} == {ap,x[-1],y[-1]}
A, B = {a,x[0],y[0]}, {ap,x[1],y[1]}
assert A.isdisjoint(B) and not any(u in Q and v in Q for Q in (A,B) for u,v in T)
N = {a,b,ap,x[0]}
assert {(u,v) for u,v in T if u in N and v in N} == {(a,ap),(b,ap),(b,x[0])}
degree = {u: sum(u!=v and (u,v) not in T and (v,u) not in T for v in V) for u in V}
assert min(degree.values()) == 1 and max(degree.values()) == degree[a] == 2*n+2
count = before = rails = 0
for positions in combinations(range(2*n), n):
    ps, I, J = set(positions), iter(x), iter(y)
    w = (b,q)+tuple(next(I) if k in ps else next(J) for k in range(2*n))
    order = {v:k for k,v in enumerate(w)}
    if any(order[u]>=order[v] for u,v in G if u in S and v in S):
        continue
    rails += 1
    for k in range(1,len(S)+1):
        without_a = w[:k]+(ap,)+w[k:]
        for j in range(k+1):
            ext = without_a[:j]+(a,)+without_a[j:]
            rank = {v:i for i,v in enumerate(ext)}
            assert all(rank[u]<rank[v] for u,v in G)
            count += 1
            before += rank[a] < rank[b]
assert (rails, count, before, Fraction(before,count)) == (162,14580,1944,Fraction(2,15))
print(f"n={n}: {rails} extensions of S; {count} extensions of P; a<b in {before}; p={Fraction(before,count)}.")
print(f"Exact minima {{a,b}}, maxima {{a',x{n-1},y{n-1}}}, min degree 1, max degree {degree[a]}, and specified induced N and disjoint antichains.")

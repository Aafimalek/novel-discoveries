"""Canonical equality diagrams of four one-low words when all lows co-occur."""
from itertools import combinations,permutations,product

g=range(4)
patterns=((1,1,1),(1,1,2),(1,2,1),(1,2,2),(1,2,3))
def renorm(words):
    maps=[{0:0} for _ in g]
    return tuple(tuple(maps[i].setdefault(x,len(maps[i]))
                       for i,x in enumerate(w)) for w in words)
canon=set()
for cols0 in product(patterns,repeat=4):
    cols=[list(col) for col in cols0]
    for i in g:
        cols[i].insert(i,0)
    W=tuple(zip(*cols))
    if any(sum(x==y for x,y in zip(u,v))>=2 for u,v in combinations(W,2)):
        continue
    canon.add(min(renorm(tuple(tuple(W[i][j] for j in perm) for i in perm))
              for perm in permutations(g)))
for W in sorted(canon):
    print(*map(lambda w:''.join(map(str,w)),W))

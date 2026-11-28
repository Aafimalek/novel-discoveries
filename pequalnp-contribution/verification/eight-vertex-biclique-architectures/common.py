from itertools import combinations, product
from functools import lru_cache
E0=[(0,3),(1,4),(2,4),(0,5),(1,5),(3,5),(1,6),(2,6),(4,6),(0,7),(2,7),(3,7),(4,7),(5,7)]
allE=list(combinations(range(8),2))
mask={a:1<<i for i,a in enumerate(allE)}
E=sum(mask[tuple(sorted(e))] for e in E0)
N=((1<<28)-1)^E
cover=[sum(v for (a,b),v in mask.items() if (s>>a&1) and (s>>b&1)) for s in range(256)]
bics={}
for d in product(range(3),repeat=8):
 l=tuple(i for i,x in enumerate(d) if x==1)
 r=tuple(i for i,x in enumerate(d) if x==2)
 if not l or not r or l>r:continue
 k=sum(mask[tuple(sorted((a,b)))] for a in l for b in r)
 c=len(l)+len(r)
 bics[k]=(c,l,r)

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
@lru_cache(None)
def biconly(G):
 opts=[[k for k in bics if (k&G)==k and k>>i&1] for i in range(28)]
 @lru_cache(None)
 def go(left):
  if not left:return 0,()
  i=(left&-left).bit_length()-1
  best=(99,())
  for k in opts[i]:
   c,p=go(left&~k)
   best=min(best,(c+bics[k][0],p+(k,)))
  return best
 return go(G)

memo={0:(0,())}
baseopts=[[k for k in bics if (k&E)==k and k>>i&1] for i in range(28)]
def edge_bicost(G):
 if G in memo:return memo[G]
 i=(G&-G).bit_length()-1
 # Must not compute an edge not in the supplied subgraph, but covered
 # prior edges may still be used in a future term. Use global E options
 # here only when explicitly using a set of REQUIRED edges.
 best=(99,())
 for k in baseopts[i]:
  c,p=edge_bicost(G&~k)
  best=min(best,(c+bics[k][0],p+(k,)))
 memo[G]=best
 return best

def info(B):return [(bics[k][0],bics[k][1],bics[k][2]) for k in B]
cost,B=edge_bicost(E)
print("best weighted monotone biclique OR cost",cost-1,info(B),flush=True)
best=99
for Q,(qc,ql,qr) in bics.items():
 H=Q&N; Qtrue=Q&E
 if not H or not Qtrue:continue
 # All edges absent from Q require a monotone term. Some induced larger
 # inputs where Q and H both hold require a true edge in this term too.
 must=E&~Q
 needs={S&E for S in cover if S&H and S&E and not S&must}
 minH,hcov=biconly(H)
 fixed=(qc-1)+(minH-1)+2 # negate, then intersect
 if fixed>=best:continue
 # General weighted hitting set of edge-mask requirements, indexed as
 # subsets of at most 14 true edges; every biclique is contained in E.
 pool=sorted(k for k in bics if not k&~E)
 need=[1<<i for i in range(28) if must>>i&1]+sorted(needs)
 hit={k:sum(1<<i for i,n in enumerate(need) if n&k) for k in pool}
 opts=[[k for k in pool if hit[k]>>i&1] for i in range(len(need))]
 @lru_cache(None)
 def hit_all(t):
  if not t:return 0,()
  i=(t&-t).bit_length()-1
  ans=99,()
  for k in opts[i]:
   c,p=hit_all(t&~hit[k])
   ans=min(ans,(c+bics[k][0],p+(k,)))
  return ans
 pc,p=hit_all((1<<len(need))-1)
 score=fixed+pc
 if score<best:
  best=score
  print("one NOT candidate",score,"Q",(ql,qr),"H",info(hcov),"P",info(p),flush=True)
print("best in this model (sentinel monotone+1 if none matched):",best)

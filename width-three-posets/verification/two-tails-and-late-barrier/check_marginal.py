from itertools import combinations
orders=[tuple('01345678'),tuple('01567834')]
comps=[(0,3,2),(0,5,2),(0,8,1),(1,6,2)]
vals=[(p[:j]+('2',)+p[j:],w) for o,k,w in comps for p in [orders[o]] for j in range(k+1)]
def count(f, sample=vals): return sum(w for o,w in sample if f(o))
def ahead(o,u,v): return o.index(u)<o.index(v)
N=count(lambda _:True)
assert N==43 and count(lambda o:ahead(o,'2','0'))==7
assert min(count(lambda o:ahead(o,u,v)) for u,v in combinations('012345678',2))==29
for c in '012345678':
 for u,v in combinations([x for x in '012345678' if x!=c],2):
  for out in [False,True]:
   A=lambda o:ahead(o,c,u) if out else ahead(o,u,c)
   B=lambda o:ahead(o,c,v) if out else ahead(o,v,c)
   assert count(A)*count(B) <= N*count(lambda o:A(o) and B(o))
S=[(o,w) for o,w in vals if ahead(o,'0','2')]
X=lambda o:ahead(o,'3','2')
Y=lambda o:ahead(o,'6','2')
assert (count(lambda _:True,S),count(X,S),count(Y,S),count(lambda o:X(o) and Y(o),S))==(36,14,9,3)
print('Exact arithmetic: late majority at 7/43; all marginal XYZ tests pass; conditional XYZ fails.')

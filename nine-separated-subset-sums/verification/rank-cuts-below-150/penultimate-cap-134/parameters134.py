"""Tiny exact audit of the new cap parameters; no phase-2 search."""
from itertools import product
from cap_moment import K,run
from anchored134 import bins

T=134
Q=tuple(run(T))
W=66-min(Q)
Y=tuple(range(T-6,T+2))
R=133-2*min(Q)
assert K==(158,159,161,162,168,169,171,172)
assert Q==tuple(range(37,65)) and W==29
assert (Q[0]+108,Q[-1]+108)==(145,172)
assert Y==tuple(range(128,136)) and Y[-1]-134==1
assert Y[2]-W==101
assert 2*W==2*(64-Q[0])+4
assert R==59
bal=[];unbal=[]
for z in product((-1,1),repeat=8):
    if z[0]!=1:continue
    k=abs(sum(a*b for a,b in zip(Y,z)))
    (bal if sum(z)==0 else unbal).append(k)
assert len(bal)==35 and len(unbal)==93
assert max(bal)==16 and min(unbal)==248
assert 149-2*Q[0]-max(bal)==R
assert min(unbal)-(151-2*Q[0])==171>R
for a in range(64,75):
    intervals=[(1,21)]*(a-64)
    intervals += [(149-2*q,151-2*q) for q in reversed(Q)]
    intervals += [(77,223)]*36 + [(278,321)]*(148-2*a) + [(375,10000)]*(a-20)
    L,U=bins(a,Q[0])
    assert len(intervals)==128
    assert list(zip(L,U))==[(60*l,60*u) for l,u in intervals]
assert sum(Y)<10000
print('Cap 134: starts 145..172; slots q37..64; W=29; x3>=29 gives r3<=101.')
print('Cap y=128..135; prior x8>=134 gives r8<=1; R>=59 (unbalanced branch R>171).')
print('All 11 exact bin capacities verified.')

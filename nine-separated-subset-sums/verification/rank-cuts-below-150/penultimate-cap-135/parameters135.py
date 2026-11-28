"""Tiny exact cap-135 parameter audit; no phase-2 search."""
from itertools import product
from cap_moment import K,run
from anchored135 import bins

T=135
Q=tuple(run(T)); W=66-min(Q); Y=tuple(range(T-6,T+2)); R=133-2*min(Q)
assert K==(158,159,161,162,168,169,171,172)
assert Q==tuple(range(38,65)) and W==28
assert (Q[0]+108,Q[-1]+108)==(146,172)
assert Y==tuple(range(129,137)) and Y[-1]-135==1
assert Y[2]-W==103
assert 2*W==2*(64-Q[0])+4
assert R==57
bal=[];unbal=[]
for z in product((-1,1),repeat=8):
    if z[0]!=1:continue
    k=abs(sum(a*b for a,b in zip(Y,z)))
    (bal if sum(z)==0 else unbal).append(k)
assert len(bal)==35 and len(unbal)==93
assert max(bal)==16 and min(unbal)==250
assert 149-2*Q[0]-max(bal)==R
assert min(unbal)-(151-2*Q[0])==175>R
for a in range(64,75):
    intervals=[(1,21)]*(a-64)
    intervals += [(149-2*q,151-2*q) for q in reversed(Q)]
    intervals += [(75,225)]*37 + [(278,321)]*(148-2*a) + [(373,10000)]*(a-20)
    L,U=bins(a,Q[0])
    assert len(intervals)==128
    assert list(zip(L,U))==[(60*l,60*u) for l,u in intervals]
assert sum(Y)<10000
print('Cap 135: starts 146..172; slots q38..64; W=28; x3>=28 gives r3<=103.')
print('Cap y=129..136; prior x8>=135 gives r8<=1; R>=57 (unbalanced branch R>175).')
print('All 11 exact bin capacities verified.')

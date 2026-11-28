"""Exact rank-slot count relaxation and affine consequences (standard Python)."""
from fractions import Fraction as F
from itertools import product
Q=(50,51,53,54,60,61,63,64)
PAIR_ENDS=(51,54,61,64)
TARGET=F(8922135,128)
TOTAL_LO=F(665929,1000)
TOP2_LO=F(19263,100)
L=(1,2,3,4,5,44,84,85)
U=tuple(range(142,150))

def admissible():
    best=None
    candidates=0
    kept=0
    for block in product(*(range(q,75) for q in PAIR_ENDS)):
        a=tuple(i for x in block for i in (x,x))
        if any(not 0<=v-u<=r-q-1
               for q,r,u,v in zip(Q,Q[1:],a,a[1:])):
            continue
        candidates+=1
        rows=[(j,t) for q,x in zip(Q,a) for j,t in
              ((x-q+1,149-2*q),(x+1,148+2*q),(149-x,447-2*q))]
        def lower(j):
            return max([2*j-1]+[t+2*(j-i) for i,t in rows if j>=i])
        if any(lower(x-q+1)>=151-2*q for q,x in zip(Q,a)): continue
        kept+=1
        z=(sum(lower(j)**2 for j in range(1,129)),a)
        best=z if best is None else min(best,z)
    return candidates,kept,best

def replay():
    candidates,kept,best=admissible()
    assert best==(8922135,(60,60,61,61,66,66,67,67))
    assert kept==264
    assert F(best[0],128)==TARGET
    total8=TOTAL_LO-149
    y=[1,2,3,4,total8-(10+147+148+149),147,148,149]
    assert sum(y)==total8
    assert all(L[i]<=y[i]<=U[i] for i in range(8))
    assert sum(t*t for t in y)<TARGET
    t=(TOP2_LO-1)/2
    assert t>=84 and 8*84-21-TOP2_LO>0
    cap=sum((t-k)**2 for k in range(7))+(TOP2_LO-t)**2
    assert cap<TARGET
    full=sum((2*p-1 if p<50 else 2*p)**2 for p in range(1,257))
    assert full==22496013
    print('Rank count tuples:',candidates,'after upper-slot envelopes:',kept)
    print('Min relaxed base square sum:',best[0],'over 128;',best[1])
    print('Base moment >=',TARGET,'; full moment >=',TARGET+149**2)
    print('Total >',TOTAL_LO,'; x7+x8 >',TOP2_LO,'; x8 >',(TOP2_LO+1)/2)

if __name__=='__main__':
    replay()

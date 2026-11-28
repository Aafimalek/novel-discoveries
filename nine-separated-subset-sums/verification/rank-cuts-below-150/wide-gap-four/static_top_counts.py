"""Tiny exact top-word compatibility enumeration; no optimizer."""
from itertools import product, combinations
Q=(50,53,60,63)
CHOICES=tuple(product(tuple(product('+-',repeat=2)),repeat=4))

def allowed(m,pat,singleton_gate):
    assigned={}
    def put(i,t):
        assert 1<=i<=64
        if i in assigned and assigned[i]!=t:return False
        assigned[i]=t
        return True
    for q,(v,w) in zip(Q,pat):
        opp='+' if w=='-' else '-'
        if not (put(q-1,v+'+-') and put(q,v+'-+') and put(q+1,opp+'++')):
            return False
    for q,(v,w) in zip(Q,pat):
        if v=='+' and q+m<=64 and not put(q+m,'-++'):return False
        if v=='-' and m<=q-3 and not put(q-1-m,'+--'):return False
        if w=='+' and m<=q-1 and not (put(q+1-m,'+-+') and put(q-m,'++-')):return False
    if singleton_gate:
        for (p,(_,wp)),(q,(_,wq)) in combinations(zip(Q,pat),2):
            if wp==wq=='-' and q-p in (m,m+1):return False
    return True

def count(m,gate):
    return sum(allowed(m,pat,gate) for pat in CHOICES)

assert len(CHOICES)==256 and count(3,False)==0
base=[count(m,False) for m in range(4,16)]
added=[count(m,True) for m in range(4,16)]
assert base==[48,24,24,24,32,4,4,32,16,32,128,128]
assert added==[48,24,12,12,32,1,1,32,8,16,128,128]
assert all(count(m,True)>0 for m in range(4,61))
for m,(a,b) in enumerate(zip(base,added),4):print(m,a,b)
print('m=3 only: no top-word assignment; counts are necessary patterns, not chambers.')

#!/usr/bin/env python3
"""Exact truth-table verification of fixed x0 frontiers."""
from itertools import product
from functools import reduce

E0=((0,3),(1,4),(2,4),(0,5),(1,5),(3,5),(1,6),(2,6),(4,6),
    (0,7),(2,7),(3,7),(4,7),(5,7))
E=tuple((1<<i)|(1<<j) for i,j in E0)
U=tuple(range(256))

def le(a,b): return a&b==a

def minima(seq):
    s=set(seq)
    return {a for a in s if not any(b!=a and le(b,a) for b in s)}

def maxima(seq):
    s=set(seq)
    return {a for a in s if not any(b!=a and le(a,b) for b in s)}

f=lambda x:any(le(e,x) for e in E)
H=lambda x:bool(x&1)
Ps=minima(x for x in U if H(x))
Qs=maxima(x for x in U if not H(x))
Is=maxima(x for x in U if not f(x))
derived=tuple([
    {e for e in E if not H(e)},
    {i for i in Is if H(i)},
    minima(e|p for e,p in product(E,Ps)),
    maxima(i&q for i,q in product(Is,Qs)),
])
exhaustive=tuple([
    minima(x for x in U if f(x) and not H(x)),
    maxima(x for x in U if not f(x) and H(x)),
    minima(x for x in U if f(x) and H(x)),
    maxima(x for x in U if not f(x) and not H(x)),
])
assert derived==exhaustive
assert tuple(map(len,derived))==(11,3,8,8)
assert len(set.union(*derived))==30
print('Verified phase-frontier sizes 11, 3, 8, 8; total 30 of 256 inputs.')
for name,F in zip(('min positive H=0','max negative H=1','min positive H=1','max negative H=0'),derived):
    print(name+':', *sorted(F))

#!/usr/bin/env python3
"""Executable five-color rule on K union rho*K; all arithmetic is exact."""
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations

# Basis (1,r,s,rs), r^2=33, s^2=-3.
def point(a=0,b=0,c=0,d=0): return tuple(map(F,(a,b,c,d)))
ZERO, ONE = point(), point(1)
def add(x,y): return tuple(a+b for a,b in zip(x,y))
def sub(x,y): return tuple(a-b for a,b in zip(x,y))
def scale(q,x): return tuple(q*a for a in x)
def conj(x): return (x[0],x[1],-x[2],-x[3])
def mul(x,y):
    u = [F(0)]*4
    for i,a in enumerate(x):
        for j,b in enumerate(y):
            f=i&j
            u[i^j] += a*b*(33 if f&1 else 1)*(-3 if f&2 else 1)
    return tuple(u)
def norm(x): return mul(x,conj(x))

@lru_cache(None)
def rootmod(D, n):
    """Square root of D mod 2^n, consistently 1 mod 4 for n >= 2."""
    assert D%8==1 and n>=1
    r=1
    for k in range(3,n+2):
        if (r*r-D) % (1<<k):
            r += 1<<(k-2)
        assert (r*r-D) % (1<<k)==0
    return r % (1<<n)

def vq(q):
    assert q
    n,d=abs(q.numerator),q.denominator
    return (n&-n).bit_length()-(d&-d).bit_length()

def poly_res(a, b, n):
    """Residue mod 2^n of the integral value a + b sqrt(33)."""
    if not n: return 0
    e=max([0]+[-vq(z) for z in (a,b) if z])
    mod=1<<(n+e)
    def modq(z):
        z=z*(1<<e)
        assert z.denominator&1
        return (z.numerator*pow(z.denominator,-1,mod))%mod
    N=(modq(a)+modq(b)*rootmod(33,n+e))%mod
    assert N%(1<<e)==0, (a,b,n)
    return N>>e

def poly_v(a,b):
    if not a and not b: return float('inf')
    e=max([0]+[-vq(z) for z in (a,b) if z])
    n=1
    while True:
        N=poly_res(a*(1<<e),b*(1<<e),n)
        if N: return vq(F(N))-e
        n*=2

def local_coords(x):
    a,b,c,d=x
    return ((a+c,b+d),(2*c,2*d))  # s = 1 + 2*zeta

@lru_cache(None)
def val(x):
    return min(poly_v(*z) for z in local_coords(x))

@lru_cache(None)
def color(side,x):
    """side=0 for x in K, side=1 for rho*x, with shared origin."""
    assert side in (0,1)
    m=val(x)
    if m>=0:
        if side==1 and m==1: return 4
        a,b=(poly_res(*z,1) for z in local_coords(x))
        return a+2*b
    h=-m
    A,B=(poly_res(a*(1<<h),b*(1<<h),h+1) for a,b in local_coords(x))
    u,v=F(A%(1<<h),1<<h),F(B%(1<<h),1<<h)
    x0=point(u-v/2,0,v/2)
    assert val(sub(x,x0))>=0 and val(x0)==m
    # Root of t^2 - 7t/4 + 1 with valuation +2; error at least 2+h.
    rprime=F(7+rootmod(-15,5+h),8)
    ystar=scale(rprime,x0)
    assert val(ystar)==m+2
    forbidden=color(1-side,ystar)
    palette=[k for k in range(5) if k!=forbidden]
    return palette[(A>>h)+2*(B>>h)]

def cross_sq(x,y):
    p=mul(x,conj(y))
    # Nonzero imaginary part contributes a nonzero j* term independent
    # over K, so the distance squared cannot be rational in this case.
    if p[2] or p[3]: return None
    return add(norm(sub(x,y)),scale(F(1,4),p))

def test():
    sites={(0,ZERO)}
    nneg=0
    for h in range(0,9):
        u=F(7+rootmod(-15,5+h),8)
        assert vq(u)==2
        w=(F(7,4)*u-2)/(1-F(7,4)*u+u*u)
        x,y=point(1+w),point(u*w)
        assert cross_sq(x,y)==ONE
        assert min(val(x),val(y))<0
        nneg+=1
        # Three norm-one directions also put different residues in each
        # relevant native coset and exercise cross edges on both sides.
        for d in (ONE,point(F(1,2),0,F(1,2)),point(F(5,6),0,0,F(1,18))):
            assert norm(d)==ONE
            A,B=mul(x,d),mul(y,d)
            for side,p in ((0,A),(1,B),(1,A),(0,B)):
                sites.add((side,p)); sites.add((side,add(p,ONE)))
            assert color(0,A)!=color(1,B) and color(1,A)!=color(0,B)
    aux=(point(0,0,F(1,6),F(1,6)),point(0,0,F(-1,6),F(1,6)))
    for s in (0,1):
        for p in (ONE,point(2),point(F(1,2),0,F(1,2)),*aux):
            sites.add((s,p))
    edges=0
    for (a,x),(b,y) in combinations(sorted(sites),2):
        sq=norm(sub(x,y)) if a==b else cross_sq(x,y)
        if sq==ONE:
            assert color(a,x)!=color(b,y), (a,x,b,y)
            edges+=1
    print(f"Exact fixture: {len(sites)} vertices, {edges} unit edges; all proper.")
    print(f"{nneg} rational parameter tests for cross unit edges at negative valuation.")
    print("Finite audit only; the infinite correctness proof is in the note.")

if __name__=="__main__":
    test()

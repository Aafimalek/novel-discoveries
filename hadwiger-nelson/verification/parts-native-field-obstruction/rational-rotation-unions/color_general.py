#!/usr/bin/env python3
"""Exact replay of the generalized h>0 two-copy coloring."""
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations
from base_color import (ONE,ZERO,point,add,sub,scale,mul,norm,conj,vq,val,
                        poly_res,local_coords)

class RotationColor:
    def __init__(self,c):
        self.c=F(c)
        assert -1 < self.c < 1
        self.lam=2*(1-self.c)
        self.h=-vq(self.lam)
        assert self.h > 0
        self.A=2*self.c*(1<<self.h)
        assert vq(self.A)==0

    @lru_cache(None)
    def small_root(self,p):
        """Rational approximation to the valuation-h root, with error >= p."""
        assert p>self.h
        n=p-self.h
        # w = t/2^h is odd and solves 2^(2h)w^2-A*w+1=0.
        mod=1<<n
        a=(self.A.numerator*pow(self.A.denominator,-1,mod))%mod
        w=1
        for k in range(1,n):
            if (w*w*(1<<(2*self.h))-a*w+1) % (1<<(k+1)):
                w+=1<<k
        assert (w*w*(1<<(2*self.h))-a*w+1)%mod==0
        ret=F(w*(1<<self.h))
        assert vq(ret)==self.h
        return ret

    @lru_cache(None)
    def color(self,side,x):
        m=val(x)
        if m>=0:
            if side==1 and m>=1 and x!=ZERO: return 4
            a,b=(poly_res(*z,1) for z in local_coords(x))
            return a+2*b
        k=-m
        R,S=(poly_res(a*(1<<k),b*(1<<k),k+1) for a,b in local_coords(x))
        u,w=F(R%(1<<k),1<<k),F(S%(1<<k),1<<k)
        x0=point(u-w/2,0,w/2)
        ystar=scale(self.small_root(max(self.h+1,k+1)),x0)
        assert val(ystar)==m+self.h
        avoid=self.color(1-side,ystar)
        return [j for j in range(5) if j!=avoid][(R>>k)+2*(S>>k)]

    def cross_sq(self,x,y):
        # In use, the imaginary part of the rotation does not belong to K.
        # Its independent term vanishes precisely when x*conj(y) is real.
        z=mul(x,conj(y))
        if z[2] or z[3]: return None
        return add(norm(sub(x,y)),scale(self.lam,z))

def run(c):
    C=RotationColor(c)
    U={(0,ZERO)}
    for k in range(1,9):
        u=C.small_root(C.h+k)
        z=(2*c*u-2)/(1-2*c*u+u*u)
        x,y=point(1+z),point(u*z)
        assert C.cross_sq(x,y)==ONE and val(x)<0
        assert val(y)==val(x)+C.h
        for d in (ONE,point(F(1,2),0,F(1,2)),point(F(5,6),0,0,F(1,18))):
            assert norm(d)==ONE
            X,Y=mul(x,d),mul(y,d)
            for s,p in ((0,X),(1,Y),(1,X),(0,Y)):
                U.add((s,p)); U.add((s,add(p,ONE)))
            assert C.color(0,X)!=C.color(1,Y) and C.color(1,X)!=C.color(0,Y)
    if C.h%2==0:
        # Standard matching reference join with integer radius 2^(h/2).
        R=point(1<<(C.h//2))
        assert C.cross_sq(R,R)==ONE
        U.add((0,R)); U.add((1,R))
    edge=0
    for (s,x),(t,y) in combinations(sorted(U),2):
        d=norm(sub(x,y)) if s==t else C.cross_sq(x,y)
        if d==ONE:
            assert C.color(s,x)!=C.color(t,y),(s,x,t,y)
            edge+=1
    print(f"Re(rho)={c}: {len(U)} vertices, {edge} unit edges; all proper.")

if __name__=="__main__":
    run(F(7,8))
    run(F(31,32)) # rho=(31+3i*sqrt(7))/32 is outside the earlier mod-11 field.

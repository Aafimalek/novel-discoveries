#!/usr/bin/env python3
"""Exact root viability for a prescribed positively oriented central sign."""
from fractions import Fraction
from itertools import product

from root_filter import interval


def coeff_bound(signs, take_min):
    # x_i starts with unit gaps plus g at the two types of necessary triggers:
    # x1 >= g+1 when epsilon1=+; and x_i-x_{i-1} >= g+1 for - to +.
    trigger = [int(signs[0] == 1)] + [
        int(a == -1 and b == 1) for a,b in zip(signs, signs[1:])
    ]
    prefix = [sum(trigger[:i+1]) for i in range(9)]
    suffix = [sum(signs[i:]) for i in range(10)]
    p6,p7,p9 = (prefix[i-1] for i in (6,7,9))
    # Nonnegative slack variables with cumulative requirements at 6, 7, 9.
    # Allocate minimum required mass at each cut and one final slack unit.
    budgets = ((38,-p6,6), (39,p6-p7,7), (63,p7-p9,9), (1,0,10))
    u = sum((i+1)*a for i,a in enumerate(signs))
    v = sum(a*t for a,t in zip(signs,prefix))
    op = min if take_min else max
    for c,m,k in budgets:
        w = op(suffix[:k])
        u += c*w
        v += m*w
    return u,v


def allowed_g(signs):
    """Closed lower, upper; the original g < 2 is applied separately."""
    lo,hi = Fraction(1),Fraction(2)
    mn=coeff_bound(signs,True)
    mx=coeff_bound(signs,False)
    # min(g) <= g <= max(g), written as c + k*g <= 0.
    for c,k in ( (mn[0],mn[1]-1), (-mx[0],1-mx[1]) ):
        if k==0:
            if c>0: return None
        elif k>0:
            hi=min(hi,Fraction(-c,k))
        else:
            lo=max(lo,Fraction(-c,k))
    return (lo,hi) if lo<=hi and lo<2 else None


def main():
    cases=list(product((-1,1),repeat=9))
    potential=[]
    for s in cases:
        a,b=interval(s,True)
        if b>=1 and a<2:
            potential.append(s)
    refined={s:z for s in potential if (z:=allowed_g(s)) is not None}
    assert all(s in potential for s in cases if allowed_g(s) is not None)
    print("Full-support sign patterns at the two-cut root:",len(cases))
    print("Could reach [1,2) from raw root extrema:",len(potential))
    print("Still viable under central-partition cuts:",len(refined))
    print("Viable with g=1:",sum(a<=1<=b for a,b in refined.values()))
    print("Viable both signs of x9:",{t:sum(s[-1]==t for s in refined) for t in (-1,1)})


if __name__=="__main__":
    main()

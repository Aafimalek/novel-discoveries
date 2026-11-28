#!/usr/bin/env python3
"""Exact labeled-order examples; the general claim uses the written proof."""
from fractions import Fraction
from itertools import pairwise


def scores(weights):
    r=[0]
    for w in weights:
        r += [x+w for x in r]
    return r


def order_and_check(weights):
    r=scores(weights)
    order=sorted(range(len(r)), key=r.__getitem__)
    assert all(r[j]-r[i]>=1 for i,j in pairwise(order))
    return order


def normalize(weights):
    before=order_and_check(weights)
    short=[i for i,(a,b) in enumerate(pairwise(weights)) if b-a<2]
    new=list(weights)
    if short:
        lo,hi=short[0],short[-1]+2
        assert short==list(range(lo,hi-1)) and 2<=hi-lo<=3
        center=sum(weights[lo:hi])/(hi-lo)
        new[lo:hi]=[center+Fraction(2*k-(hi-lo-1),2) for k in range(hi-lo)]
    assert order_and_check(new)==before
    assert max(new)<=max(weights)
    assert sum(new)==sum(weights) and all(b-a==1 or b-a>=2 for a,b in pairwise(new))
    return new


if __name__=='__main__':
    for nums in [('3','10','30','31.5'),('2.3','3.4','4.6','30'),('7','8.25','9.5','60','120')]:
        xs=list(map(Fraction,nums))
        ys=normalize(xs)
        assert ys!=xs
        print(', '.join(map(str,xs)), '->', ', '.join(map(str,ys)))

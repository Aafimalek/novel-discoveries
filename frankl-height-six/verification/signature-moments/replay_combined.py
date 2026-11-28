#!/usr/bin/env python3
"""Exact tangent screen followed by exhaustive residual integer counts."""
import argparse
from math import comb
from check_bounds import H,screens
from tangent_screen import rows,search


def check(k):
    assert 3*k+comb(k-2,2)>H(k-1)
    unexcluded={}
    total=0
    for r,S,Z in rows(k):
        d=search(k,r,S,Z)
        if d is None:
            unexcluded.setdefault(r,[]).append(S)
        else:
            total+=1
    survivors=0
    for r,allowed in unexcluded.items():
        counts,alive=screens(k,r,allowed)
        survivors+=len(alive)
        if alive:
            print(f"  max block {r}; sample remaining count rows {alive[:4]}",flush=True)
    print(f"k={k}: {total} tangent-certified (r,S), "
          f"{sum(len(v) for v in unexcluded.values())} residual (r,S), "
          f"{survivors} surviving count vectors",flush=True)
    return survivors


def main():
    p=argparse.ArgumentParser()
    p.add_argument("first",type=int,default=14,nargs="?")
    p.add_argument("last",type=int,default=29,nargs="?")
    p.add_argument("--require-none",action="store_true")
    a=p.parse_args()
    assert 14<=a.first<=a.last<=60
    result=[check(k) for k in range(a.first,a.last+1)]
    if a.require_none:
        assert not any(result)


if __name__=="__main__":
    main()

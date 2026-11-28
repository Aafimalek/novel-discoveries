#!/usr/bin/env python3
"""Count-free rational tangent certificates for the weighted moment."""
from fractions import Fraction
from itertools import combinations
from math import comb,floor,ceil
import argparse,json
from pathlib import Path
from check_bounds import H,smallbound


def kap(s):
    return comb(s,2)-1


def saved_lower(k,s):
    return comb(k-2,2)-comb(s-2,2)+kap(s)-H(k+1-s)+3*k


def data(k,r,S):
    results={}
    for s in range(3,r+1):
        E=smallbound(k,r,s,comb(k-2,2)-comb(s-2,2)+kap(s)-S)
        if E is not None:
            a=comb(s-1,2)
            results[s]=(s*a,s*a*a+a*E,kap(s))
    return results


def witness_check(k,r,S,d,Z):
    """All inequalities checked by integer cross multiplication."""
    m,M,K=Z[r]
    initial=2*d*m-k*M-d*d
    left=S-K
    return all(initial*Ks+left*(2*d*ms-k*Ms)>0 for ms,Ms,Ks in Z.values())


def search(k,r,S,Z):
    m,M,K=Z[r]
    left=S-K
    terms=list(Z.values())
    probes={0}
    for ms,_,Ks in terms:
        p=Fraction(m)+Fraction(left*ms,Ks)
        probes.update((floor(p),ceil(p)))
    for (a,X,P),(b,Y,Q) in combinations(terms,2):
        den=2*(a*Q-b*P)
        if den:
            p=Fraction(k*(X*Q-Y*P),den)
            probes.update((floor(p),ceil(p)))
    return next((d for d in sorted(probes) if d>=0 and witness_check(k,r,S,d,Z)),None)


def rows(k):
    rmax=max(b for b in range(2,k) if H(k+1-b)>=3*k)
    for r in range(3,rmax+1):
        if smallbound(k,r,r) is None:
            continue
        Slo=max(kap(r),saved_lower(k,r))
        Shi=comb(k,2)*kap(r)//comb(r,2)
        for S in range(Slo,Shi+1):
            Z=data(k,r,S)
            if r not in Z:
                continue
            yield r,S,Z


def generate(k):
    cert={}
    miss=[]
    for r,S,Z in rows(k):
        d=search(k,r,S,Z)
        if d is None:
            miss.append((r,S))
        else:
            cert[(r,S)]=d
    print(f"k={k}: {len(cert)} exact tangent exclusions; {len(miss)} unexcluded (r,S) pairs",flush=True)
    if miss:
        print("  first:",miss[:12],flush=True)
    return cert,miss


def main():
    p=argparse.ArgumentParser()
    p.add_argument("first",type=int,default=14,nargs="?")
    p.add_argument("last",type=int,default=32,nargs="?")
    p.add_argument("--save",type=Path)
    a=p.parse_args()
    table={}
    for k in range(a.first,a.last+1):
        cert,miss=generate(k)
        table[k]=[[r,S,d] for (r,S),d in sorted(cert.items())]
    if a.save:
        a.save.write_text(json.dumps(table,separators=(",",":"))+"\n")


if __name__=="__main__":
    main()

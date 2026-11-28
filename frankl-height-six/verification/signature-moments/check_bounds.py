#!/usr/bin/env python3
"""Replay a necessary-integer-inequality screen for one-isolate block designs.

All arithmetic integer. See README for the combinatorial implications. A
surviving row is only a vector of block counts, not a design or counterexample.
"""
from itertools import combinations
from functools import lru_cache
from bisect import bisect_left,bisect_right
from math import comb
import argparse


def exceeds_min_squares(total,n,upper):
    if n==0:
        return total>0
    q,r=divmod(total,n)
    return (n-r)*q*q+r*(q+1)**2>upper


@lru_cache(maxsize=None)
def min_link_with_pair_deficit(k,s,sizes,missing):
    """Lower bound on links at an s-block from near-exhaustion of point pairs."""
    # Each of its vertices is already on this s-block; count other blocks.
    # A size-t block consumes t-1 pairs through the vertex and contributes
    # choose(t-1,2) links if it differs from the selected block.
    n=k-s
    d=[None]*(n+1)
    d[0]=0
    for a in range(1,n+1):
        v=[d[a-(t-1)]+comb(t-1,2) for t in sizes if t-1<=a and d[a-(t-1)] is not None]
        if v:
            d[a]=min(v)
    missing=min(missing,s*n)
    prev={0:0}
    for _ in range(s):
        nxt={}
        for used,val in prev.items():
            for deficit in range(min(n,missing-used)+1):
                a=d[n-deficit]
                if a is not None:
                    key=used+deficit
                    nxt[key]=min(nxt.get(key,val+a),val+a)
        prev=nxt
        if not prev:
            return None
    return min(prev.values())


def H(n):
    return 1+n+comb(n,2)


def ceil(a,b):
    assert b>0
    return -((-a)//b)


@lru_cache(maxsize=None)
def smallbound(k,r,b,seed=0):
    """Return a link cap for size b, or None if b impossible."""
    h=k-b
    d=max(0,ceil(k-3-2*(r-2),r-1))
    W=max(seed,ceil((k-2)*d,r))
    cap=H(h+1)-3*k
    while W<=cap:
        c=next(c for c in range(h+1) if H(c+1)>=3*k+W)
        E=comb(h-c+1,2) if c>=1 else comb(h,2)
        new=(b-2)*h-((b-2)*E)//b+ceil(comb(h,2)-E,comb(r,2))
        if new<=W:
            return E
        W=new
    return None


def caps_for(k,r):
    return {s:smallbound(k,r,s) for s in range(3,r+1)}


def candidates(k,r,allowed=None):
    """All count vectors for sizes 3..r with N_r>0 and (optionally) allowed savings."""
    def go(s,available,pairs,saved):
        if allowed is not None:
            start=bisect_left(allowed,saved+int(s==r)*(comb(s,2)-1))
            if start==len(allowed) or allowed[start]>saved+available*(comb(s,2)-1)//comb(s,2):
                return
        if s==3:
            low=int(s==r)
            high=available//3
            if allowed is None:
                for n in range(low,high+1):
                    yield tuple(pairs+[(3,n)])
            else:
                for score in allowed[bisect_left(allowed,saved+2*low):
                                     bisect_right(allowed,saved+2*high)]:
                    if (score-saved)%2==0:
                        yield tuple(pairs+[(3,(score-saved)//2)])
        else:
            for n in range(int(s==r),available//comb(s,2)+1):
                yield from go(s-1,available-n*comb(s,2),pairs+[(s,n)],
                              saved+n*(comb(s,2)-1))
    return go(r,comb(k,2),[],0)


def screens(k,r,allowed=None):
    cap=caps_for(k,r)
    # Probe the given largest size without assuming the existence of smaller ones.
    if cap[r] is None:
        return {"none":0}, []
    base={s:x for s,x in cap.items() if x is not None}
    saving_min=comb(k-2,2)-comb(r-2,2)+comb(r,2)-1-H(k+1-r)+3*k
    alpha={s:comb(s-1,2) for s in base}
    reject={"absent":0,"savings":0,"count caps":0,"global moment":0,"pair deficit":0,"small support":0,"survives":0}
    alive=[]
    for counts in candidates(k,r,allowed):
        x={s:n for s,n in counts if n}
        if any(s not in base for s in x):
            reject["absent"]+=1
            continue
        saved=sum((comb(s,2)-1)*n for s,n in x.items())
        if saved<saving_min:
            reject["savings"]+=1
            continue
        E={s:smallbound(k,r,s,comb(k-2,2)-comb(s-2,2)+comb(s,2)-1-saved)
           for s in x}
        if None in E.values():
            reject["count caps"]+=1
            continue
        sizes=tuple(x)
        per_s={s:(s*alpha[s]*x[s], (s*alpha[s]**2+alpha[s]*E[s])*x[s],
                  comb(s,2)*x[s]) for s in sizes}
        DT=sum(a for a,_,_ in per_s.values())
        UT=sum(b for _,b,_ in per_s.values())
        if exceeds_min_squares(DT,k,UT):
            reject["global moment"]+=1
            continue
        choices=[z for q in range(1,len(sizes)+1) for z in combinations(sizes,q)]
        totals={J:tuple(sum(per_s[s][i] for s in J) for i in range(3)) for J in choices}
        if any(exceeds_min_squares(D,k,U) for D,U,_ in totals.values()):
            reject["global moment"]+=1
            continue
        missing=comb(k,2)-sum(v[2] for v in per_s.values())
        if any((need:=min_link_with_pair_deficit(k,s,tuple(sorted(sizes)),missing)) is None or
               need>E[s] for s in sizes):
            reject["pair deficit"]+=1
            continue
        bad=False
        for s,n in x.items():
            # Two blocks in this size group cannot share more than one vertex.
            # Each one contributes alpha[s] links to the other.
            I=min(comb(n,2), n*(E[s]//alpha[s])//2)
            # The actual number of intersecting block pairs could be any I0
            # in this range. Exclude only if each such I0 is impossible.
            viable_occupancy=False
            for I0 in range(max(0,s*n-k),I+1):
                R=min(k,k-(s*n-I0))
                lost=n*E[s]-2*I0*alpha[s]
                def fits(J,D,U,P):
                    hit_bound=sum(x[t]*alpha[t]*min(t,E[t]//alpha[s]) for t in J)
                    budget=min(lost,hit_bound)
                    return (not exceeds_min_squares(max(0,D-budget),R,U) and
                            P-(2*budget)//(min(J)-2)<=comb(R,2))
                if all(fits(J,D,U,P) for J,(D,U,P) in totals.items() if s not in J):
                    viable_occupancy=True
                    break
            if not viable_occupancy:
                bad=True
                break
        if bad:
            reject["small support"]+=1
            continue
        reject["survives"]+=1
        alive.append(x)
    return reject,alive


def run(k):
    # Already forced by a height-three Sauer counting bound on any block's
    # uncompressed support, with just baseline 3k.
    rmax=max(b for b in range(2,k) if H(k+1-b)>=3*k)
    print(f"k={k}: initial max block {rmax}")
    overall=[]
    for r in range(rmax,2,-1):
        value,alive=screens(k,r)
        if "none" in value:
            print(f"  r={r} eliminated by refined caps")
        else:
            print(f"  r={r} cap {caps_for(k,r)}, tests {value}")
        if alive:
            print(f"    first survivors {alive[:4]}")
            overall.append((r,alive))
    assert 3*k+comb(k-2,2)>H(k-1)  # All blocks are pairs.
    return overall


if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("first",type=int,default=14,nargs="?")
    p.add_argument("last",type=int,default=25,nargs="?")
    a=p.parse_args()
    assert 14<=a.first<=a.last<=30
    for k in range(a.first,a.last+1):
        run(k)

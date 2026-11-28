#!/usr/bin/env python3
from collections import Counter
from functools import cache
from root_filter import BASE,CUTS,interval

@cache
def capped_interval(signs, strengthened=True, cap=None):
    if cap is None:
        return interval(signs, strengthened)
    if not (85 <= cap <= 148):
        raise ValueError('need 85 <= cap <= 148')
    suffix=[0]*10
    for k in range(8,-1,-1):
        suffix[k]=suffix[k+1]+signs[k]
    const=sum((k+1)*c for k,c in enumerate(signs))
    pre=((38,6),(39,7)) if strengthened else ()
    # Reserve the excess above the x8 cap at gap 9. The optional final
    # unit may be allocated only to gap 9 or the slack gap 10 without
    # loss: if placed earlier, exchange it with a mandatory unit at 9.
    forced_pre=77 if strengthened else 0
    free=cap-8-forced_pre
    fixed=140-forced_pre-free
    budgets=[(v,suffix[:j]) for v,j in pre]+[
        (free,suffix[:9]),(fixed,suffix[8:9]),(1,suffix[8:10])]
    return (const+sum(n*min(a) for n,a in budgets),
            const+sum(n*max(a) for n,a in budgets))

@cache
def categories(d,strengthened,cap):
    lo1,hi1=capped_interval(d+(1,),strengthened,cap)
    lo2,hi2=capped_interval(d+(0,),strengthened,cap)
    lo3,hi3=capped_interval(d+(-1,),strengthened,cap)
    al=0
    for i,(s1,s2,s3) in enumerate(((-1,-1,-1),(1,-1,-1),(1,1,-1),(1,1,1))):
        if ((lo1<=-1 if s1<0 else hi1>=1)
            and (lo2<=-1 if s2<0 else hi2>=1)
            and (lo3<=-1 if s3<0 else hi3>=1)):
            al|=1<<i
    return al

def hall_counts_for_mask(A, strengthened, cap=None):
    counts=[0]*16
    for B in BASE:
        if A != B:
            al=categories(tuple(y-x for x,y in zip(A,B)),strengthened,cap)
            counts[al]+=1
    return [sum(counts[t] for t in range(16) if t&~T==0) for T in range(16)]

def profile(r):
    for f in range(109):
        j=r-1-2*f
        if 0<=j<=147:
            n=(f,j,147-j,108-f)
            yield tuple(sum(n[i] for i in range(4) if T>>i&1) for T in range(16))

@cache
def profiles(r):
    return tuple(profile(r))

def admits(C,r):
    return any(all(a<=b for a,b in zip(C,N)) for N in profiles(r))

def layers(ranks,strengthened=True,cap=None):
    ranks=tuple(ranks)
    X={r:[] for r in ranks}
    for i,A in enumerate(BASE):
        C=hall_counts_for_mask(A,strengthened,cap)
        for r in ranks:
            if admits(C,r):X[r].append(i)
    return X

@cache
def step(A,B,cap):
    if A==B:return False
    d=tuple(y-x for x,y in zip(BASE[A],BASE[B]))
    # In a consecutive forced run, d is at least 1 and d <= M-147.
    # Independent exact bounds on d and d-M are necessary, not sufficient.
    return (capped_interval(d+(0,),True,cap)[1] >= 1 and
            capped_interval(d+(-1,),True,cap)[0] <= -147)

def chain_filter(X, cap):
    reached=None
    counts=[]
    for r in sorted(X):
        layer=X[r]
        reached=layer if reached is None else [
            b for b in layer if any(step(a,b,cap) for a in reached)]
        counts.append(len(reached))
    return counts

def main():
    for strong in (False,True):
        X=layers(CUTS,strong)
        vals=tuple(map(len,X.values()))
        assert vals==(75,76,78,76,79,77,78,79)
        print('root',strong,vals,flush=True)
    cap=121 # floor(x8)<=120 implies x8<121
    X=layers(range(131,173),True,cap)
    print('cap 121, all 42 rank layers:',[len(X[r]) for r in X],flush=True)
    print('chain-forward necessary survivors:',chain_filter(X,cap),flush=True)

if __name__=='__main__': main()

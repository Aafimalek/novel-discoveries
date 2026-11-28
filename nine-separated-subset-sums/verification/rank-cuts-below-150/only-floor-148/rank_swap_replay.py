"""Necessary rank matching for the two largest coordinates; no solver."""
CUTS=(158,159,161,162,168,169,171,172)
M=149

def starts(t):
    low=set(CUTS)
    for k in CUTS:
        low.update(range(max(109,k+t-148),k+1))
    return low

def span_low(t):
    A=starts(t)
    n=max(A)-min(A)+1
    return min(A),max(A),n,n-len(A)

def violates_rounding_band(t,s):
    ell=min(s,513-t-s)
    return 257-t <= ell <= 177

def edges(t,D):
    A=starts(t)
    S=A | {365-s for s in A}
    for s in sorted(S):
        poss=[]
        for h in range(max(1,148-t),D+1):
            if s-h not in S and (h!=148-t or not violates_rounding_band(t,s)):
                poss.append((0,s-h))
            if s+h not in S and (h!=148-t or not violates_rounding_band(t,s+h)):
                poss.append((1,s+h))
        yield s,tuple(poss)

def match_options(rows):
    opts=dict(rows); ass={}
    def aug(s,seen):
        for v in opts[s]:
            if v in seen:continue
            seen.add(v)
            if v not in ass or aug(ass[v],seen):
                ass[v]=s
                return True
        return False
    for s in sorted(opts,key=lambda i:len(opts[i])):
        if not aug(s,set()):return False
    return True

def witness_span(t):
    S=starts(t)
    k=sorted(S)
    best=None
    for i,a in enumerate(k):
        for j in range(i,len(k)):
            b=k[j]
            L=b-a+1
            H=L-(j-i+1)
            slack=L-(2*(M-t)+3*H)
            z=(slack,a,b,L,H)
            if best is None or z>best:
                best=z
    return best

if __name__=='__main__':
    possible={}
    for t in range(135,149):
        slack,a,b,L,H=witness_span(t)
        Ds=tuple(D for D in range(1,150-t) if match_options(edges(t,D)))
        print(t,(a,b),'L',L,'holes',H,'capacity gap',slack,'matching gap floors',Ds)
        assert (slack>0)==(136<=t<=147)
        if Ds:possible[t]=Ds
    assert possible=={135:(14,),148:(1,)}
    k0=(158,161,168,171)
    gap_sites=sorted([k+1 for k in k0]+[365-k for k in k0])
    assert len(set(gap_sites))==8 and all(158<=j<306 for j in gap_sites)
    print('Surviving floors under the necessary rank test:',possible)
    print('Eight distinct gap indices for floor 148:',gap_sites)

    classes={}
    for k in k0:
        rows=((k,0),(k+1,1),(k+2,1),(k+147,1),(k+148,1),(k+149,0))
        for j,v in rows:
            for r in (j,513-j):
                if r in classes:assert classes[r]==v
                classes[r]=v
    singletons=[r for r in range(158,306) if classes.get(r)==0
                and (r==158 or classes.get(r-1)==1)
                and (r==305 or classes.get(r+1)==1)]
    assert singletons==[158,161,171,196,206]
    assert (148-3+len(singletons)+3)//4==38
    print('Outer singletons in [158,305]:',singletons)
    print('Disjoint excess charges at least 38, hence 39*(d-1) <= M-148.')

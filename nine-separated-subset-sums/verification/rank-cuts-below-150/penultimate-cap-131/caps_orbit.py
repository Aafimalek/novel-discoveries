"""Exact deficit-cell and sign orbit replay; cap 131 or 132."""
import argparse
from bisect import bisect_right
from functools import lru_cache
from itertools import product
from cap127_safe import probe, bins, match
from cap_moment import envelope
from orbit import orbits, orbit_size_cut

Q=60
SIGS=tuple(s for s in product((-1,1),repeat=8) if s[0]==1)

def ceildiv(a,b):
    assert b>0
    return -(-a//b)

@lru_cache(None)
def sign_data(t,k):
    Y=tuple(range(t-6,t+2))
    ans=[]
    for S in SIGS:
        f=[Q*sum(S[k:k+j])//j for j in range(1,9-k)]
        ans.append(((sum(a*b for a,b in zip(Y,S)))*Q,S[:k],min(f),max(f)))
    return tuple(ans)

def certificates(t, W, lows, highs, tail_lo, tail_hi):
    lo=list(lows); hi=list(highs)
    N=8-len(lo)
    c=hi[-1]
    for j in range(1,N+1):
        lo.append(max(0,(tail_lo-(j-1)*c)//(N-j+1)))
        hi.append(min(c,ceildiv(tail_hi,j)))
    g=0
    for j in range(7):
        if hi[j]-lo[j+1]<(W-1)*Q:
            g|=1<<j
    for j in range(2):
        if (t-6+j)*Q-lo[j]<W*Q:
            g|=1<<(7+j)
    return g

def full_allowed(t,lows,highs,lo,hi,bl,br):
    ans=[]
    k=len(lows)
    for val,signs,m,M in sign_data(t,k):
        below=min(m*lo,m*hi)//Q
        above=ceildiv(max(M*lo,M*hi),Q)
        z0=val-above;z1=val-below
        for l,r,s in zip(lows,highs,signs):
            if s==1:
                z0-=r;z1-=l
            else:
                z0+=l;z1+=r
        low=0 if z0<=0<=z1 else min(abs(z0),abs(z1))
        high=max(abs(z0),abs(z1))
        i=bisect_right(br,low)
        j=bisect_right(bl,high)-1
        if i>j:return None
        ans.append((i,j))
    return ans

@lru_cache(None)
def orbit_groups(a,g,allowed_labels):
    # 3 capacities: a, b-a, 128-b. Bitset records middle count per first count.
    m=148-2*a
    keep=(1<<(m+1))-1
    active=[1]+[0]*a
    for O,z in zip(orbits(g),allowed_labels):
        w=len(O)
        active=[((p if z&4 else 0) | (((p<<w)&keep) if z&2 else 0) |
                 (active[j-w] if z&1 and j>=w else 0)) for j,p in enumerate(active)]
        if not any(active): return False
    return bool(active[a]&(1<<m))

def apply_orbits(a,g,ab):
    if not g:return True
    b=148-a
    M=[(1 if i<a else 0) | (2 if a<b and i<b and j>=a else 0) |
       (4 if j>=b else 0) for i,j in ab]
    masks=[]
    for O in orbits(g):
        z=7
        for i in O:z&=M[i]
        if not z:return False
        masks.append(z)
    return orbit_groups(a,g,tuple(masks))

def refine(t,profs,k):
    # Invariant: parent lists contain k-1 fixed unit deficit lower/upper
    # endpoints in whole units, and their remaining sum interval at scale 60.
    q0=t-97; W=66-q0; Rlower=133-2*q0
    Y=tuple(range(t-6,t+2))
    D0={a:sum(v*v for v in Y)-lo for lo,a in envelope(t)}
    # Each 128*D is an integer, so just use integer division in hot loops.
    D128={a:int(128*v) for a,v in D0.items()}
    assert all(D0[a]*128==v for a,v in D128.items())
    counts=[0]*6;out={}
    for a,bs in sorted(profs.items()):
        bl,br=bins(a,q0)
        for ll,hh,Tlo,Thi in bs:
            # Sign flips in the first two coordinates give easy divisibility.
            s=sum(int(y-l<W) for y,l in zip(Y[:2],ll[:2]))
            if a%(2**s):counts[0]+=1;continue
            cap=min(hh[-1],Y[2]-W)
            pLoss=sum(2*y*l-l*l for y,l in zip(Y,ll))
            ss=sum(hh)
            for C in range(cap+1):
                Cu=min(C+1,cap)
                loss=pLoss+2*Y[k-1]*C-C*C
                lo=max(0,Tlo-Q*Cu,(Rlower-ss-Cu)*Q)
                hi=min(Q*(8-k)*Cu,Thi-Q*C,
                       ceildiv((D128[a]-128*loss)*Q,128*(2*Y[k]-Cu)))
                counts[1]+=1
                if hi<lo:
                    counts[2]+=1;continue
                l=ll+(C,);h=hh+(Cu,)
                lows=tuple(Q*q for q in l);highs=tuple(Q*q for q in h)
                g=certificates(t,W,lows,highs,lo,hi)
                if not orbit_size_cut(a,g):
                    counts[3]+=1;continue
                allowed=full_allowed(t,lows,highs,lo,hi,bl,br)
                if not allowed:
                    counts[4]+=1;continue
                # Check orbit memberships before match (match mutates its input).
                if not apply_orbits(a,g,allowed):
                    counts[5]+=1;continue
                if not match(allowed):
                    counts[4]+=1;continue
                out.setdefault(a,[]).append((l,h,lo,hi))
    print('depth',k,'counts [divisibility, cells, tail, orbit-size, interval, orbit-assignment]',
          counts,'remain',[(a,len(v)) for a,v in out.items()],flush=True)
    return out

def main():
    p=argparse.ArgumentParser()
    p.add_argument('cap',choices=[131,132],type=int)
    p.add_argument('--depth',default=4,type=int,choices=[3,4,5,6])
    args=p.parse_args();t=args.cap
    R=probe(t)
    R={a:[((A,B),(A+1,B+1),lo,hi) for A,B,lo,hi in v] for a,v in R.items()}
    for k in range(3,args.depth+1):
        R=refine(t,R,k)
        if not R:break
    nz=sum(map(len,R.values()))
    print('Residual profiles',nz,{a:v[:4] for a,v in R.items()},flush=True)

if __name__=='__main__':main()

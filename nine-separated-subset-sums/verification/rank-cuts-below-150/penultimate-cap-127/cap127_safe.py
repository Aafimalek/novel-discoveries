"""First two phases of the cap-127 exact proof; the residuals need phase 3."""
from fractions import Fraction as F
from itertools import product
from cap_moment import cap, run
L=60
def summary(t):
 y=tuple(range(t-6,t+2)); forms=[]
 for s in product((-1,1),repeat=8):
  if s[0]!=1: continue
  prefs=[L*sum(s[2:2+j])//j for j in range(1,7)]
  forms.append((sum(x*z for x,z in zip(y,s)),s[1],min(prefs),max(prefs)))
 return y,forms
def first_cells(t):
 scale=1
 y,forms=summary(t)
 _,_,D,_=cap(t)
 X=scale*L
 crude=D/y[0]
 neededR=2*t-113 if t <= 126 else 0 # from pigeonhole on >=127-t unbalanced forms below rank alpha
 q0=min(run(t))
 scaleD=scale*scale*D
 upper=-((-crude*X)//1)
 counts=[0]*5; remain=[]
 for a in range((t-7)*scale):
  Aa=2*y[0]*a*scale-a*a
  if Aa>scaleD: break
  for b in range(a+1):
   counts[0]+=1
   Bb=2*y[1]*b*scale-b*b
   rem=scaleD-Aa-Bb
   if rem<0:
    counts[1]+=1; continue
   w=2*y[2]*scale-(b+1)
   lo=max(0,neededR*X-(a+b+2)*L)
   hi=min(6*(b+1)*L, -((-rem*L)//w),upper-(a+b)*L)
   if hi<lo:
    counts[2]+=1; continue
   # Rounding up tail interval coefficients independently when needed.
   ds=[]
   for base,sg,pmin,pmax in forms:
    zm=min(pmin*lo,pmin*hi)//L
    zx=-(-max(pmax*lo,pmax*hi)//L)
    blo=(b if sg>0 else -b-1)*L
    bhi=(b+1 if sg>0 else -b)*L
    vl=base*X-(a+1)*L-bhi-zx
    vh=base*X-a*L-blo-zm
    low=0 if vl<=0<=vh else min(abs(vl),abs(vh))
    high=max(abs(vl),abs(vh))
    # allowed slots q satisfy low < (151-2q)X and high >= (149-2q)X
    left=max(q0,-((high-149*X)//(2*X)))
    right=min(64,(151*X-low-1)//(2*X))
    if left<=right: ds.append((left,right))
   if len(ds)<65-q0:
    counts[3]+=1; continue
   # Distinct forms with integer consecutive slot intervals; take earliest deadline.
   ds.sort(key=lambda p:p[1])
   for q in range(q0,65):
    k=next((i for i,(u,v) in enumerate(ds) if u<=q<=v),None)
    if k is None:
     counts[3]+=1;break
    ds.pop(k)
   else:
    counts[4]+=1;remain.append((a,b,lo,hi))

 if t==127: assert counts==[7260,0,0,931,6329]
 print(t,'| coarse cells, moment rejects, tail rejects, matching rejects, remain:',counts)
 return remain


from fractions import Fraction as F
from bisect import bisect_left,bisect_right
from heapq import heappush,heappop
from cap_moment import envelope


def ceil(x):return -((-x)//1)

def capR(D,y,t):
    R=D/y
    c=t-7
    def loss0(z): return 2*y*z-((z//c)*c*c+(z%c)**2)

    for z in range(1,R.numerator//R.denominator+1):
        if loss0(z)>D:
            R=z;break
    if 2*t-20-R<23:return R
    def loss(z):return 2*y*z-(z*z if z<=39 else (z*z+39**2)/2)
    for z in range(1,int(R)+1):
        if loss(F(z))>D:return z
    return R

def bins(a,q0):
    L=[];U=[]
    def add(c,l,r):
        assert c>=0
        L.extend([l]*c);U.extend([r]*c)
    add(a-64,1,21)
    for q in range(64,q0-1,-1):add(1,149-2*q,151-2*q)
    add(q0-1,151-2*q0,149+2*q0)
    add(148-2*a,278,321)
    add(a-20,449-2*q0,10000)
    assert len(L)==len(U)==128
    assert L==sorted(L) and U==sorted(U)
    return [x*60 for x in L],[x*60 for x in U]

def match(allowed):
    if len(allowed)!=128:return False
    allowed.sort()
    H=[];j=0
    for k in range(128):
        while j<128 and allowed[j][0]<=k:
            heappush(H,allowed[j][1]);j+=1
        if not H or heappop(H)<k:return False
    return True

def probe(t):
    cells=first_cells(t)
    Y,forms=summary(t)
    q0=t-97
    caps={a:sum(v*v for v in Y)-v for v,a in envelope(t)}
    profs={}
    for a,D in caps.items():
        if D<0:continue
        upper=ceil(capR(D,Y[0],t)*60)
        lefts,rights=bins(a,q0)
        profs[a]=(D,upper,lefts,rights)
    remains={};counts=[0]*3
    for a,b,_l,_h in cells:
        Aa=2*Y[0]*a-a*a
        Bb=2*Y[1]*b-b*b
        for k,(D,upper,lefts,rights) in profs.items():
            counts[0]+=1
            Tlo=max(0,((2*t-113 if t <= 126 else 0)-a-b-2)*60)
            rem=D-Aa-Bb
            w=2*Y[2]-(b+1)
            Thi=min(6*(b+1)*60,ceil(rem*60/w),upper-(a+b)*60)
            if Thi<Tlo:
                counts[1]+=1;continue
            allowed=[]
            for base,sg,pmin,pmax in forms:
                zm=min(pmin*Tlo,pmin*Thi)//60
                zx=-(-max(pmax*Tlo,pmax*Thi)//60)
                blo=(b if sg>0 else -b-1)*60
                bhi=(b+1 if sg>0 else -b)*60
                vl=(base-a-1)*60-bhi-zx
                vh=(base-a)*60-blo-zm
                low=0 if vl<=0<=vh else min(abs(vl),abs(vh))
                high=max(abs(vl),abs(vh))
                j0=bisect_right(rights,low)
                j1=bisect_right(lefts,high)-1
                if j0>j1:break
                allowed.append((j0,j1))
            if not match(allowed):counts[2]+=1;continue
            remains.setdefault(k,[]).append((a,b,Tlo,Thi))
    if t==127: assert counts==[69619,0,69525] and {a:len(v) for a,v in remains.items()}=={64:45,65:29,66:15,67:5}
    print(t,'| profiles', counts, 'remain',[(a,len(v)) for a,v in remains.items()])
    return remains
if __name__=='__main__':
 import sys
 for t in map(int,sys.argv[1:]):probe(t)

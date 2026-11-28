"""Coarse two-deficit cells for the cap shards, exploratory unless all cells reject."""
from fractions import Fraction as F
from itertools import product
from cap_moment import cap, crude_deduction, run
L=60
def summary(t):
 y=tuple(range(t-6,t+2)); forms=[]
 for s in product((-1,1),repeat=8):
  if s[0]!=1: continue
  prefs=[L*sum(s[2:2+j])//j for j in range(1,7)]
  forms.append((sum(x*z for x,z in zip(y,s)),s[1],min(prefs),max(prefs)))
 return y,forms
def calc():
 t,scale=119,1
 y,forms=summary(t)
 _,_,D,_=cap(t)
 X=scale*L
 crude=F(crude_deduction(t)[3])
 neededR=2*t-113 # from pigeonhole on >=127-t unbalanced forms below rank alpha
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
 assert counts==[6328,1597,2631,2100,0]
 assert remain==[]
 print('cap 119 | unit cells, moment rejects, tail rejects, matching rejects, remain:',counts)

if __name__=='__main__':
 calc()

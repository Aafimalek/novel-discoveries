from itertools import product
from bisect import bisect_right
from cap127_safe import probe,bins,match,ceil,summary
from cap_moment import envelope

def calc(t):
 q0=t-97; small=66-q0; Rlower=133-2*q0
 profs=probe(t)
 y,_=summary(t)
 D0={a:sum(v*v for v in y)-lo for lo,a in envelope(t)}
 forms=[]
 for sg in product((-1,1),repeat=8):
   if sg[0]!=1:continue
   prefixes=[60*sum(sg[3:3+j])//j for j in range(1,6)]
   forms.append((sum(a*b for a,b in zip(sg,y)),sg[1],sg[2],min(prefixes),max(prefixes)))
 results=[0]*4;survive=[]
 for a,boxes in profs.items():
  lefts,rights=bins(a,q0)
  D=D0[a]
  for A,B,Tlo,Thi in boxes:
   s=int(y[0]-A<small)+int(y[1]-B<small)
   if a%(2**s):results[0]+=1;continue
   lo0=2*y[0]*A-A*A+2*y[1]*B-B*B
   for C in range(min(B,y[2]-small)+1):
    Cu=min(C+1,y[2]-small)
    loss=lo0+2*y[2]*C-C*C
    lo=max(0,Tlo-60*Cu,(Rlower-A-B-2-Cu)*60)
    hi=min(60*5*Cu,Thi-60*C,ceil((D-loss)*60/(2*y[3]-Cu)))
    results[1]+=1
    if hi<lo:
     results[2]+=1
     continue
    allowed=[]
    for base,sg,tg,pmin,pmax in forms:
     zm=(pmin*(lo if pmin>=0 else hi))//60
     zx=-((-(pmax*(hi if pmax>=0 else lo)))//60)
     blo,bhi=((B,B+1) if sg>0 else (-B-1,-B))
     clo,chi=((C,Cu) if tg>0 else (-Cu,-C))
     vl=(base-A-1-bhi-chi)*60-zx
     vh=(base-A-blo-clo)*60-zm
     low=0 if vl<=0<=vh else min(abs(vl),abs(vh))
     high=max(abs(vl),abs(vh))
     j0=bisect_right(rights,low);j1=bisect_right(lefts,high)-1
     if j0>j1:break
     allowed.append((j0,j1))
    if not match(allowed):
     results[3]+=1
     continue
    survive.append((a,A,B,C,lo,hi))

 print('third boxes parity/profile, total, loss, matching',results)
 print('not excluded',len(survive),survive[:20])
 return survive
if __name__=='__main__':
 import sys
 calc(int(sys.argv[1]))

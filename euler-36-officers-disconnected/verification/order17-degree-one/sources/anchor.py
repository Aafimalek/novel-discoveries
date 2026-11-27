import anchored_base as base
from pysat.solvers import Solver
from pysat.card import CardEnc
from itertools import combinations, permutations, product
import sys
N=int(sys.argv[1]); M=int(sys.argv[2]); solver=sys.argv[3]
arg=sys.argv[4] if len(sys.argv)>4 else 'all'
case=arg
high_anchor=int(arg.split(':')[-1]) if M==2 and arg!='all' else None
custom=tuple(tuple(map(int,w)) for w in sys.argv[5:])
prefix=[max([0]+[w[i] for w in custom])+1 for i in range(4)]
F,W,P,D=base.build_encoding(6,N,M,high_anchor=high_anchor,fixed_prefix=prefix)
for w in custom: F.append([W[w]])
case += '-' + '_'.join(sys.argv[5:])
v=range(6); gs=range(4); cp=tuple(combinations(gs,2))
def p(i,j,a,b):return P[i,j,a,b] if i<j else P[j,i,b,a]
for word,w in W.items():
 F.append([p(i,j,word[i],word[j]) for i,j in cp])
 F.append([-w,*(D[g,word[g]][2] for g in gs)])
for g in gs:
 e=[D[g,a][d] for a in v for d in range(M+1,7)]
 F.extend(CardEnc.equals(e,bound=N-M*6,top_id=F.nv).clauses)
if M==1:
 for g in range(1,4):
  for a in range(1,6): F.append([D[g,a][2]])
 for i,k,h in permutations(range(1,4)):
  for a in range(1,6):
   F.append([D[i,a][3],-p(i,k,a,0)]+([-D[h,0][2]] if N==17 else []))
 for i in (1,2):
  for d in range(2,7): F.append([-D[i,0][d],D[i+1,0][d]])
 if arg!='all':
  for i,d in ([(3,int(arg))] if len(arg)==1 else enumerate(map(int,arg),1)):
   F.append([D[i,0][d]])
   if d<6: F.append([-D[i,0][d+1]])
 for i,j in combinations(range(1,4),2):
  h=6-i-j
  for pi in permutations(range(1,6)):
   F.append([-D[h,0][N-15+1],*(p(i,j,a,b) for a,b in zip(range(1,6),pi))])
  for di,dj in product(range(1,7),repeat=2):
   if di+dj+25>2*N:
    F.append([-D[i,0][di],-D[j,0][dj]])
if M==2 and len(sys.argv)>4 and sys.argv[4]!='all':
 q=int(arg.split(':')[0])
 F.append([D[0,5][high_anchor]])
 if high_anchor<6: F.append([-D[0,5][high_anchor+1]])
 for g in gs:
  highs=[D[g,a][3] for a in v]
  F.extend(CardEnc.atleast(highs,bound=q,top_id=F.nv).clauses)
 for a in v:
  F.append([D[0,a][3] if a>=6-q else -D[0,a][3]])
# Sharper rectangle propagation. Threshold literals are at-least.
for i,j in cp:
 for h,k in [tuple(set(gs)-{i,j}),tuple(reversed(tuple(set(gs)-{i,j})))]:
  for a,b,c in product(v,repeat=3):
   for dx,dy in product(range(M,4),repeat=2):
    d=6-dx-dy
    if d>M:
     F.append([p(i,j,a,b),p(i,h,a,c),p(j,h,b,c),D[i,a][dx+1],D[j,b][dy+1],D[h,c][d]])
    if d+1>M:
     for t in v:
      F.append([p(i,j,a,b),p(i,h,a,c),p(j,h,b,c),D[i,a][dx+1],D[j,b][dy+1],-p(i,k,a,t),-p(j,k,b,t),D[h,c][d+1]])
print(N,M,solver,F.nv,len(F.clauses),flush=True)

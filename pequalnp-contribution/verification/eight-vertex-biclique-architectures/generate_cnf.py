from pathlib import Path
from itertools import combinations
from common import E, allE, bics, mask
import sys
valid={k:v for k,v in bics.items() if not k&~E}
subs=sorted({sum(1<<i for i in side) for _,a,b in valid.values() for side in (a,b) if len(side)>1})
ids=0
def fresh():
 global ids
 ids+=1
 return ids
S={s:fresh() for s in subs}
B={k:fresh() for k in valid}
C=[]
for k,(c,a,b) in valid.items():
 for side in (a,b):
  if len(side)>1:C.append([-B[k],S[sum(1<<i for i in side)]])
for e in allE:
 if E&mask[e]:C.append([v for k,v in B.items() if k&mask[e]])
for s in subs:
 choices=[]
 sub=[u for u in range(1,s) if u&s==u]
 for t,u in combinations(sub,2):
  if t|u!=s: continue
  var=[S[z] for z in (t,u) if z.bit_count()>1]
  if not var:
   choices=None
   break
  if len(var)==1:choices+=var
  else:
   h=fresh()
   C.extend([[-h,v] for v in var])
   choices.append(h)
 if choices is not None:C.append([-S[s],*choices])
bound=int(sys.argv[1])+1
pick=[*S.values(),*(v for b in B.values() for v in (b,b))]
prev=[]
for x in pick:
 state=[fresh() for j in range(bound+1)]
 C.append([-x,state[0]])
 for v,w in zip(prev,state): C.append([-v,w])
 for v,w in zip(prev,state[1:]): C.append([-x,-v,w])
 C.append([-state[-1]])
 prev=state
target=Path('monoshared'+sys.argv[1]+'.cnf')
target.write_text('p cnf %s %s\n'%(ids,len(C))+''.join(' '.join(map(str,c))+' 0\n' for c in C))

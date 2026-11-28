#!/usr/bin/env python3
"""Bounded root propagation via exact strict/nonstrict Farkas leaves."""
from argparse import ArgumentParser
from fractions import Fraction
import json
from pathlib import Path
from central_matching import newcuts, parse
from central_root_lp import verify

LIMIT=5 # New pivotal comparisons per still-live root.
TRIALS=8 # Max attempted comparisons per step.
STRICT={12,18} # x9 <= 150 and g <= 2, before any matching or branch rows.

def bounds(s,mask,high):
    d=[s[i] if (mask>>i)&1 else 0 for i in range(9)]
    return ([a-z for a,z in zip(s,d)],-1) if high else (d,-1)

def arrays(s,path):
    A,b,_=newcuts(s,True)
    assert A[12]==[0]*8+[1] and b[12]==150
    assert A[18]==list(s) and b[18]==2
    for mask,high in path:
        assert 0<mask<511 and mask&1 and high in (0,1)
        row,rhs=bounds(s,mask,high)
        A.append(row);b.append(rhs)
    return A,b

def exact(A,b,sparse):
    assert all(str(int(i))==i and int(i) in range(len(b)) for i in sparse)
    y=[Fraction(sparse.get(str(i),0)) for i in range(len(b))]
    return (all(v>=0 for v in y) and
        all(sum(a[i]*v for a,v in zip(A,y))==0 for i in range(9)) and
        (sum(r*v for r,v in zip(b,y))<0 or
         sum(r*v for r,v in zip(b,y))==0 and any(y[i]>0 for i in STRICT)))

def oracle(s,path,extra=()):
    import numpy as np
    from scipy.optimize import linprog
    A,b=arrays(s,path)
    for row,rhs in extra:
        A.append(row);b.append(rhs)
    C=[int(i in STRICT) for i in range(len(b))]
    opts=dict(method='highs')
    opt=linprog([0]*9+[-1],A_ub=np.column_stack((A,C)),b_ub=b,
                bounds=[(None,None)]*9+[(0,None)],**opts)
    if opt.status==0 and opt.x[-1]>1e-8:
        return opt.x[:9],None
    if opt.status==2:
        dual=linprog(np.zeros(len(A)),A_eq=np.vstack((np.array(A).T,b)),b_eq=[0]*9+[-1],
                     bounds=[(0,None)]*len(A),**opts)
        if dual.status!=0: return None,None
        v=dual.x
    elif opt.status==0:
        v=-opt.ineqlin.marginals
    else:
        return None,None
    for den in (1000,10000,100000,1000000):
        y=[Fraction(float(x)).limit_denominator(den) for x in v]
        sparse={str(i):str(q) for i,q in enumerate(y) if q}
        if exact(A,b,sparse):
            return None,sparse
    return None,None

def candidates(s,x,path):
    g=sum(a*z for a,z in zip(s,x))
    used={p[0] for p in path}
    result=[]
    for m in range(1,511,2): # central-support complement pairs, one representative
        if m in used: continue
        d=sum(a*x[i] for i,a in enumerate(s) if (m>>i)&1)
        violation=min(d+1,g+1-d)
        if violation>1e-7: result.append((-violation,m))
    return [m for _,m in sorted(result)[:TRIALS]]

def compute(sign):
    s=parse(sign); path=[]; steps=[]
    x,cert=oracle(s,path)
    if cert is not None: return {'steps':[],'terminal':cert}
    while x is not None and len(steps)<LIMIT:
        for mask in candidates(s,x,path):
            both=[oracle(s,path+[(mask,q)]) for q in (0,1)]
            c0,c1=[p[1] for p in both]
            if c0 is None and c1 is None: continue
            if c0 is not None and c1 is not None:
                return {'steps':steps,'terminal_pair':[mask,c0,c1]}
            rejected=int(c1 is not None)
            steps.append([mask,rejected,both[rejected][1]])
            path.append((mask,1-rejected))
            x=both[1-rejected][0]
            break
        else: break
    return {'steps':steps}

def replay(base,records):
    discharged=0; removed=0; strict=0
    assert all(sign not in base and len(sign)==9 and set(sign)<=set('+-') for sign in records)
    def checked(s,path,leaf):
        nonlocal strict
        A,b=arrays(s,path)
        assert exact(A,b,leaf)
        strict+=int(sum(r*Fraction(leaf.get(str(i),0)) for i,r in enumerate(b))==0)
    for sign,record in records.items():
        s=parse(sign);path=[]
        assert set(record) in ({'steps'},{'steps','terminal'},{'steps','terminal_pair'})
        for m,d,cert in record['steps']:
            assert d in (0,1)
            checked(s,path+[(m,d)],cert)
            removed+=1
            path.append((m,1-d))
        if 'terminal' in record:
            checked(s,path,record['terminal'])
            discharged+=1
        if 'terminal_pair' in record:
            m,c0,c1=record['terminal_pair']
            checked(s,path+[(m,0)],c0)
            checked(s,path+[(m,1)],c1)
            discharged+=1
    print('Additional whole orientations rejected:',discharged)
    print('Unresolved orientations:',512-len(base)-discharged)
    print('Propagated one-sided central comparisons:',removed)
    print('Leaves needing the original strict inequalities:',strict)
    print('Orientations with additional certified restrictions:',len(records))
    print('Complete rejections:',','.join(sign for sign,r in records.items() if 'terminal' in r or 'terminal_pair' in r))

def main():
    p=ArgumentParser()
    p.add_argument('--verify-only',action='store_true')
    a=p.parse_args()
    base_all=json.loads(Path('central-root-farkas.json').read_text())
    assert verify(base_all['True'],True)==294
    base=base_all['True']['verified_rejections']
    path=Path('branch-farkas.json')
    if a.verify_only: records=json.loads(path.read_text())
    else:
        records={}
        from itertools import product
        for s in product('-+',repeat=9):
            sign=''.join(s)
            if sign in base: continue
            r=compute(sign)
            if r!={'steps':[]}: records[sign]=r
        path.write_text(json.dumps(records,sort_keys=True,separators=(',',':'))+'\n')
    replay(base,records)
if __name__=='__main__': main()

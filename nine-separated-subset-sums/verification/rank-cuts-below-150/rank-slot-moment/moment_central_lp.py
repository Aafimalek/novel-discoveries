"""Check exact rational Farkas certificates for rank-moment root cuts."""
import argparse
from fractions import Fraction
from itertools import product
import json
from pathlib import Path
from central_root_lp import verify
from central_matching import parse
from central_branch import arrays, exact, oracle
from rank_moment_arithmetic import TARGET,TOTAL_LO,TOP2_LO,L,U,replay

def cuts():
    s_row=([-1000]*9,-665929)
    xy_row=([0]*6+[-100,-100,0],-19263)
    # x_i^2 <= (L_i+U_i)x_i - L_i U_i (affine upper secant).
    coeff=[-128*(a+b) for a,b in zip(L,U)]+[0]
    rhs=-(TARGET*128+128*sum(a*b for a,b in zip(L,U)))
    assert Fraction(rhs).denominator==1
    return [s_row,xy_row,(coeff,int(rhs))]

def rational_on_support(A, b, indices, strict_case):
    """Use floating support merely as a hint; return only exact feasible duals."""
    if not indices: return None
    cols=[[A[i][j] for i in indices] for j in range(9)]
    cols.append([b[i] for i in indices])
    rhs=[0]*9+[0 if strict_case else -1]
    if strict_case:
        cols.append([int(i in (12,18)) for i in indices])
        rhs.append(1)
    R=[[Fraction(t) for t in (row+[val])] for row,val in zip(cols,rhs)]
    rr=0; pivots=[]
    k=len(indices)
    for c in range(k):
        rrnew=next((j for j in range(rr,len(R)) if R[j][c]),None)
        if rrnew is None: continue
        R[rr],R[rrnew]=R[rrnew],R[rr]
        y=R[rr][c];R[rr]=[z/y for z in R[rr]]
        for j in range(len(R)):
            if j!=rr and R[j][c]:
                y=R[j][c]
                R[j]=[a-y*d for a,d in zip(R[j],R[rr])]
        pivots.append(c);rr+=1
    if any(row[-1] and not any(row[:-1]) for row in R): return None
    d={str(indices[c]):str(R[j][-1]) for j,c in enumerate(pivots) if R[j][-1]}
    return d if exact(A,b,d) else None

def scaled_oracle(s):
    import numpy as np
    from scipy.optimize import linprog
    A,b=arrays(s,[])
    for row,rhs in cuts(): A.append(row);b.append(rhs)
    factors=np.array([max(1,max(abs(i) for i in a),abs(z)/150) for a,z in zip(A,b)])
    D=np.asarray(A)/factors[:,None]; r=np.asarray(b)/factors
    C=np.array([int(i in (12,18)) for i in range(len(b))])/factors
    l=linprog([0]*9+[-1],A_ub=np.column_stack((D,C)),b_ub=r,
              bounds=[(None,None)]*9+[(0,None)],method='highs')
    if l.status==0 and l.x[-1]>1e-8: return l.x[:9],None
    if l.status==2:
        q=linprog(np.zeros(len(b)),A_eq=np.vstack((D.T,r)),b_eq=[0]*9+[-1],
                  bounds=[(0,None)]*len(b),method='highs')
        if q.status!=0: return None,None
        w=q.x; strict_case=False
    elif l.status==0:
        w=-l.ineqlin.marginals; strict_case=True
    else: return None,None
    for tol in (1e-8,1e-10,1e-13,0.0):
        ids=[i for i,v in enumerate(w) if v>tol]
        proof=rational_on_support(A,b,ids,strict_case)
        if proof is not None: return None,proof
    return None,None

def compute(base):
    out={};left=0;unknown=0
    for k in map(''.join,product('-+',repeat=9)):
        if k in base: continue
        x,cert=oracle(parse(k),[],cuts())
        if x is None and cert is None: x,cert=scaled_oracle(parse(k))
        if cert is not None: out[k]=cert
        elif x is not None: left+=1
        else: unknown+=1
    return {'certs':out,'unknown':unknown,'numerical_feasible':left}

def verify_new(base,result):
    strict=0
    for k,y in result['certs'].items():
        assert k not in base and len(k)==9 and set(k)<=set('+-')
        A,b=arrays(parse(k),[])
        e=cuts()
        rhs=b+[t for _,t in e]
        assert exact(A+[row for row,_ in e],rhs,y)
        strict+=int(sum(bi*Fraction(y.get(str(i),0)) for i,bi in enumerate(rhs))==0)
    print('New exact full-orientation exclusions:',len(result['certs']),
          '| not excluded by baseline plus these bounds:',512-len(base)-len(result['certs']),
          '| strict-bound certificates:',strict,'| numerical unknown:',result['unknown'])

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--verify-only',action='store_true')
    a=p.parse_args()
    replay()
    old=json.loads(Path('central-root-farkas.json').read_text())['True']
    assert verify(old,True)==294
    base=old['verified_rejections']
    path=Path('moment-farkas.json')
    if a.verify_only: data=json.loads(path.read_text())
    else:
        data=compute(base)
        path.write_text(json.dumps(data,sort_keys=True,separators=(',',':'))+'\n')
    verify_new(base,data)

if __name__=='__main__':
    main()

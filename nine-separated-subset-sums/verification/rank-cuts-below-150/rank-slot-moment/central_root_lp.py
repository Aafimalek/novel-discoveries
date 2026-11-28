#!/usr/bin/env python3
"""Find and replay exact Farkas certificates for central-sign root cuts."""
import argparse,json
from fractions import Fraction
from itertools import product
from pathlib import Path


def unit(i):
    return [int(j==i) for j in range(9)]


def sub(a,b):
    return [x-y for x,y in zip(a,b)]


def inequalities(s, with_packing=True):
    """Every row is of the form a*x <= b. Close x9<150 and g<2."""
    A=[[-x for x in unit(0)]] + [sub(unit(i-1),unit(i)) for i in range(1,9)]
    b=[-1]*9
    A.extend([[-x for x in unit(5)],[-x for x in unit(6)],
              [-x for x in unit(8)],unit(8),[-1]*9])
    b.extend([-44,-84,-149,150,-511])
    if with_packing:
        for d in range(1,5):
            paired_lower=set(range(7,7-2*d,-2))
            A.append([1 if i in paired_lower else -1 for i in range(9)])
            b.append(-(2**(9-d)-1))
    A.extend([list(s),[-x for x in s]])
    b.extend([2,-1])
    if s[0]==1:
        A.append(sub(s,unit(0)))
        b.append(-1)
    for i in range(1,9):
        if s[i-1]==-1 and s[i]==1:
            A.append(sub(s,sub(unit(i),unit(i-1))))
            b.append(-1)
    return A,b


def check(A,b,y):
    return len(A)==len(y) and all(v>=0 for v in y) and all(
        sum(a[i]*v for a,v in zip(A,y))==0 for i in range(9)
    ) and sum(z*v for z,v in zip(b,y))<0


def compute(with_packing=True):
    import numpy as np
    from scipy.optimize import linprog
    rejects={}
    feasible=0
    uncertain=0
    for s in product((-1,1),repeat=9):
        A,b=inequalities(s,with_packing)
        primal=linprog(np.zeros(9),A_ub=A,b_ub=b,bounds=[(None,None)]*9,method="highs")
        if primal.status==0:
            feasible+=1
            continue
        if primal.status!=2:
            uncertain+=1
            continue
        Aeq=np.vstack((np.array(A).T,b))
        beq=[0]*9+[-1]
        dual=linprog(np.zeros(len(A)),A_eq=Aeq,b_eq=beq,bounds=[(0,None)]*len(A),method="highs")
        if dual.status!=0:
            uncertain+=1
            continue
        for den in (10**3,10**4,10**5,10**6,10**7):
            y=[Fraction(float(x)).limit_denominator(den) for x in dual.x]
            if check(A,b,y):
                rejects["".join("+" if x==1 else "-" for x in s)]=[str(v) for v in y]
                break
        else:
            uncertain+=1
    return {"verified_rejections":rejects,"numerical_feasible":feasible,"unresolved":uncertain}


def verify(data,with_packing):
    rejected=data["verified_rejections"]
    for name,rows in rejected.items():
        assert len(name)==9 and set(name)<={"+","-"}
        A,b=inequalities(tuple(1 if x=="+" else -1 for x in name),with_packing)
        assert check(A,b,[Fraction(v) for v in rows])
    return len(rejected)


def main():
    p=argparse.ArgumentParser()
    p.add_argument("certificates",type=Path)
    p.add_argument("--verify-only",action="store_true")
    a=p.parse_args()
    if a.verify_only:
        r=json.loads(a.certificates.read_text())
    else:
        r={str(w):compute(w) for w in (False,True)}
        a.certificates.write_text(json.dumps(r,sort_keys=True,separators=(",",":"))+"\n")
    for f in (False,True):
        d=r[str(f)]
        n=verify(d,f)
        print("With pairing cuts:" if f else "Without pairing cuts:",
              512-n,"not excluded;",n,"exact Farkas exclusions.")
    if not a.verify_only:
        assert all(v["unresolved"]==0 for v in r.values())


if __name__=="__main__":
    main()

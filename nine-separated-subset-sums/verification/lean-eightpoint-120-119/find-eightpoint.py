"""Untrusted LP finder plus exact integers for one designated (a,b)."""
from scipy.optimize import linprog
from scipy.sparse import csr_matrix
from itertools import product
import math,sys,json
def solve(a,b,p):
    anchors=list(range(-800+((p-a-b)%2),801,2))
    offs=[s*148+t*a+u*b for s,t,u in product((-1,1),repeat=3)]
    if len(set(offs))!=8:raise ValueError("Fixed weights already collide")
    V=sorted({abs(c+d) for c in anchors for d in offs})
    vidx={x:i+1 for i,x in enumerate(V)}
    rows=[]; cols=[]; vals=[]; rhs=[]
    for i,c in enumerate(anchors):
        pat=[c+d for d in offs]
        rows += [i]*9
        cols += [0]+[vidx[abs(x)] for x in pat]
        vals += [1]+[-1]*8
        rhs.append(sum(x*x for x in pat))
    C=csr_matrix((vals,(rows,cols)),shape=(len(anchors),len(V)+1))
    res=linprog([-64]+[1 if not x else 2 for x in V],A_ub=C,b_ub=rhs,bounds=(0,None),method='highs')
    if not res.success:raise RuntimeError(res.message)
    mu={x:max(0,math.ceil(res.x[vidx[x]]-1e-8)) for x in V}
    mu={x:k for x,k in mu.items() if k}
    lam=min(sum((c+d)**2+mu.get(abs(c+d),0) for d in offs) for c in anchors)
    assert 8*(801**2+148**2+a*a+b*b)>=lam
    debit=sum((1 if not x else 2)*v for x,v in mu.items())
    B=(64*lam-debit+511)//512
    return dict(a=a,b=b,parity=p,penalty=list(mu.items()),budget=debit,bound=B,**{'lambda':lam})
a,b=map(int,sys.argv[1:]); print(json.dumps([solve(a,b,p) for p in range(2)],separators=(',',':')))

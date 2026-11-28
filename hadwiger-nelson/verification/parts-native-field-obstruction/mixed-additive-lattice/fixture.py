#!/usr/bin/env python3
"""Exact generation and independent model audit of the Parts alpha/beta pilot."""
import argparse
from itertools import combinations,product
from pathlib import Path
from hashlib import sha256
import json

DEN=24
Z=(0,)*8
ONE=(1,)+(0,)*7
TWO=(2*DEN,)+(0,)*7
RAD=(33,-3,-7)
CW=((0,0),(2,0),(1,1),(-1,1),(-2,0),(-1,-1),(1,-1))

def add(x,y):
    return tuple(a+b for a,b in zip(x,y))

def sub(x,y):
    return tuple(a-b for a,b in zip(x,y))

def mul(x,y):
    z=[0]*8
    for i,a in enumerate(x):
        for j,b in enumerate(y):
            c=a*b
            for t,r in enumerate(RAD):
                if (i&j)&(1<<t):c*=r
            z[i^j]+=c
    return tuple(z)

def bar(x):
    return tuple(-a if (i&6).bit_count()==1 else a for i,a in enumerate(x))

def scale(x,k):
    return tuple(k*a for a in x)

def sumset(A,B):
    return {add(x,y) for x in A for y in B}

def generate():
    # Independent exact construction of the same point set:
    # first use sparse closed formulas, then generic ring multiplication.
    W={(12*a,0,12*b,0,0,0,0,0) for a,b in CW}
    A={(-6*b,2*a,2*a,2*b,0,0,0,0) for a,b in CW}
    B={(9*a,0,9*b,0,3*a,0,3*b,0) for a,b in CW}
    T=sumset(W,W)
    pts=sorted(sumset(sumset(T,A),B))
    w2=[(a,0,b,0,0,0,0,0) for a,b in CW]
    alpha6=(0,1,1,0,0,0,0,0)
    beta4=(3,0,0,0,1,0,0,0)
    assert mul(alpha6,bar(alpha6))==scale(ONE,36)
    assert mul(beta4,bar(beta4))==scale(ONE,16)
    # Reconstruct W as 0 plus all six powers of (1+sqrt(-3))/2.
    m=ONE
    powers={Z}
    for k in range(6):
        d=2**k
        assert all(v*2%d==0 for v in m)
        powers.add(tuple(v*2//d for v in m))
        m=mul(m,w2[2])
    assert m==scale(ONE,64) and powers==set(w2) and len(powers)==7
    eq=set()
    for a,b,c,d in product(w2,repeat=4):
        eq.add(add(scale(add(a,b),12),add(scale(mul(alpha6,c),2),scale(mul(beta4,d),3))))
    assert len(T)==19 and len(pts)==len(set(pts))<=931 and set(pts)==eq
    assert Z in eq and TWO in eq and all(not p[5] and not p[7] for p in pts)
    assert mul(TWO,bar(TWO))==scale(ONE,4*DEN**2)
    return pts

def edge_form(d):
    a,b,c,e,f,g,h,j=d
    assert not g and not j
    return (a*a+33*b*b+3*c*c+99*e*e+7*f*f+21*h*h,
            2*(a*b+3*c*e),2*(a*h-c*f),2*(b*h-e*f))

def graph(P):
    E=[]; constant_candidates=0
    # This covers the complete graph. In the chosen support the exact
    # squared norm lies in the real degree-4 subfield with masks 0,1,6,7.
    for i,j in combinations(range(len(P)),2):
        d=sub(P[i],P[j])
        c= d[0]**2+33*d[1]**2+3*d[2]**2+99*d[3]**2+7*d[4]**2+21*d[6]**2
        if c!=DEN**2:continue
        constant_candidates+=1
        form=edge_form(d)
        generic=mul(d,bar(d))
        assert generic==(form[0],form[1],0,0,0,0,form[2],form[3])
        if generic==scale(ONE,DEN**2):E.append((i,j))
    assert len(E)==len(set(E))
    return E,constant_candidates

def var(i,k):
    return 5*i+k+1

def cnf(n,E,x,z):
    for i in range(n):
        yield [var(i,k) for k in range(5)]
        for k,l in combinations(range(5),2):
            yield [-var(i,k),-var(i,l)]
    for i,j in E:
        for k in range(5):yield [-var(i,k),-var(j,k)]
    # Fix both terminals to color zero, wlog by a palette permutation.
    yield [var(x,0)]; yield [var(z,0)]

def generate_files(out):
    P=generate()
    E,n0=graph(P)
    i,j=P.index(Z),P.index(TWO)
    assert (min(i,j),max(i,j)) not in E
    out.mkdir(exist_ok=False)
    g={'scale':DEN,'generator_squares':RAD,'base_order':'bitmask 33,-3,-7',
       'vertices':P,'unit_edges':E,'terminals':[i,j]}
    gp=out/'exact-graph.json'
    gp.write_text(json.dumps(g,separators=(',',':'))+'\n')
    clauses=list(cnf(len(P),E,i,j))
    cp=out/'equal.cnf'
    with cp.open('w') as f:
        print('p cnf',5*len(P),len(clauses),file=f)
        for row in clauses:print(*row,0,file=f)
    r={'vertices':len(P),'exact_pair_tests':len(P)*(len(P)-1)//2,
       'constant_norm_screen_hits':n0,'unit_edges':len(E),'terminal_ids':[i,j],
       'cnf_variables':5*len(P),'cnf_clauses':len(clauses),
       'graph_sha256':sha256(gp.read_bytes()).hexdigest(),
       'cnf_sha256':sha256(cp.read_bytes()).hexdigest()}
    (out/'generation.json').write_text(json.dumps(r,indent=2)+'\n')
    print(r,flush=True)

def check_model(out,model):
    t=model.read_text().splitlines()
    status=[s for s in t if s.startswith('s ')]
    if status!=['s SATISFIABLE']:
        print(f'UNKNOWN (no verified positive witness); reported status {status}')
        return
    g=json.loads((out/'exact-graph.json').read_bytes())
    P=[tuple(p) for p in g['vertices']]
    E=[tuple(e) for e in g['unit_edges']]
    assert P==generate()
    assert len(P)==len(set(P)) and len(E)==len(set(E))
    # Independently reconstruct all exact edges from the coordinate set:
    # use a precomputed norm-form expression for all coefficients, instead
    # of trusting the CNF or solver's edge set.
    V=(DEN**2,0,0,0)
    U={(i,j) for i,j in combinations(range(len(P)),2)
       if edge_form(sub(P[i],P[j]))==V}
    assert U==set(E)
    for i,j in U:assert mul(sub(P[i],P[j]),bar(sub(P[i],P[j])))==scale(ONE,DEN**2)
    i,j=g['terminals']
    assert P[i]==Z and P[j]==TWO and (min(i,j),max(i,j)) not in U
    literals=[int(x) for row in t if row.startswith('v ') for x in row.split()[1:] if x!='0']
    n=5*len(P)
    assert len(literals)==n and sorted(map(abs,literals))==list(range(1,n+1))
    a={abs(x):x>0 for x in literals}
    colors=[]
    for x in range(len(P)):
        q=[k for k in range(5) if a[var(x,k)]]
        assert len(q)==1
        colors.append(q[0])
    assert colors[i]==colors[j]==0
    assert all(colors[u]!=colors[v] for u,v in U)
    assert all(any(a[abs(s)]==(s>0) for s in c) for c in cnf(len(P),E,i,j))
    (out/'checked-model.json').write_text(json.dumps({'terminals':[i,j],'colors':colors},separators=(',',':'))+'\n')
    print(f'Checked complete proper coloring: {len(P)} distinct exact sites, {len(U)} unit edges, both terminals color zero.')

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('mode',choices=('generate','check'))
    p.add_argument('out',type=Path)
    p.add_argument('model',type=Path,nargs='?')
    a=p.parse_args()
    if a.mode=='generate':
        assert a.model is None
        generate_files(a.out)
    else:
        assert a.model is not None
        check_model(a.out,a.model)

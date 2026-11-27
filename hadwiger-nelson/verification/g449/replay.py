#!/usr/bin/env python3
"""Independent exact geometry and 5-color calibration for Heule–Przybocki G449."""
from argparse import ArgumentParser
from itertools import combinations
from pathlib import Path
import hashlib
import json

N=42
D=49
# Phi_42(X), low coefficients first.
PHI=(1, 1, 0, -1, -1, 0, 1, 0, -1, -1, 0, 1, 1)
K=len(PHI)-1
EXPECTED_FILE_SHA256='58a45c4e653ff63e0218e1dec988e0a532905969dda3fc7bf84a3c83874a3848'

def rem42(f):
    t=list(f)
    for i in range(len(t)-1,K-1,-1):
        y=t[i]
        if y:
            for j,z in enumerate(PHI):
                t[i-K+j]-=y*z
    return tuple(t[:K]+[0]*max(0,K-len(t)))

def norm_poly(v):
    # Laurent polynomial f(X) f(X^-1), lifted into Z[X] using X^42=1.
    p=[0]*N
    for i,x in enumerate(v):
        if x:
            for j,y in enumerate(v):
                if y: p[(i-j)%N]+=x*y
    return p

def verify(input):
    data=input.read_bytes()
    if EXPECTED_FILE_SHA256:
        assert hashlib.sha256(data).hexdigest()==EXPECTED_FILE_SHA256
    header,*tail=data.decode("ascii").splitlines()
    assert header.split()==["K21",str(N),str(K),str(D),"449"]
    rows=[list(map(int,row.split())) for row in tail]
    assert len(rows)==449 and all(len(row)==K+1 for row in rows)
    pts=[tuple(row[:K]) for row in rows]
    colors=[row[K] for row in rows]
    assert len(set(pts))==449 and set(colors)==set(range(5))
    # Test the essential period relation used to remove negative exponents.
    assert rem42([-1]+[0]*41+[1])==(0,)*K
    unit=(D*D,)+(0,)*(K-1)
    edges=[]
    polys={}
    for i,j in combinations(range(len(pts)),2):
        d=tuple(a-b for a,b in zip(pts[i],pts[j]))
        d=min(d,tuple(-x for x in d))
        yes=polys.get(d)
        if yes is None:
            yes=polys[d]=rem42(norm_poly(d))==unit
        if yes:
            assert colors[i]!=colors[j], f'color conflict at edge {(i,j)}'
            edges.append((i,j))
    assert len(edges)==2198
    adj=[set() for _ in pts]
    for i,j in edges:
        adj[i].add(j); adj[j].add(i)
    triangles=sum(len(adj[i]&adj[j]) for i,j in edges)//3
    assert triangles==483
    print(f'coordinate SHA-256 {hashlib.sha256(data).hexdigest()}')
    print(f'{len(pts)} distinct points; {len(pts)*(len(pts)-1)//2} exact pair comparisons; {len(edges)} edges; {triangles} triangles')
    print(f'{len(polys)} difference classes up to sign; {sum(polys.values())} unit direction classes; supplied 5-coloring verified')
    return pts,edges

def cnf4(n,edges):
    def var(v,c): return 4*v+c+1
    clauses=[tuple(var(v,c) for c in range(4)) for v in range(n)]
    clauses.extend((-var(v,c),-var(w,c)) for v,w in edges for c in range(4))
    return clauses

def read_sparse6(path):
    data=path.read_bytes().strip()
    if data.startswith(b'>>sparse6<<'): data=data[11:]
    assert data[:1]==b':'
    six=[x-63 for x in data[1:]]
    assert all(0<=x<64 for x in six)
    if six[0] < 63: n,i=six[0],1
    else:
        assert six[1]<63
        n,i=(six[1]<<12)+(six[2]<<6)+six[3],4
    bits=''.join(f'{x:06b}' for x in six[i:])
    stride=1+(n-1).bit_length()
    v=0
    edges=set()
    for k in range(0,len(bits)-stride+1,stride):
        b=bits[k]=='1'
        x=int(bits[k+1:k+stride],2)
        v+=b
        if x>=n or v>=n: break
        if x>v: v=x
        else:
            assert x<v and (x,v) not in edges
            edges.add((x,v))
    return n,sorted(edges)

def main():
    ap=ArgumentParser(description=__doc__)
    ap.add_argument('input',type=Path,nargs='?',default=Path('G449.k21'))
    ap.add_argument('--sparse6',type=Path,help='optional independent sparse6 edge-data comparison')
    ap.add_argument('--cnf',type=Path)
    ap.add_argument('--edges-json',type=Path)
    args=ap.parse_args()
    pts,edges=verify(args.input)
    if args.sparse6:
        n, listed=read_sparse6(args.sparse6)
        assert n==len(pts) and listed==edges
        print('published sparse6 data match all exact edges')
    if args.cnf:
        clauses=cnf4(len(pts),edges)
        with args.cnf.open('w') as f:
            f.write(f'p cnf {4*len(pts)} {len(clauses)}\n')
            for c in clauses: f.write(' '.join(map(str,c))+' 0\n')
        print(f'bare four-color CNF: {4*len(pts)} vars, {len(clauses)} clauses')
    if args.edges_json:
        args.edges_json.write_text(json.dumps(edges,separators=(',',':'))+'\n')

if __name__=='__main__':
    main()

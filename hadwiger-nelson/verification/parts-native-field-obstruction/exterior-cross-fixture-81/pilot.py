#!/usr/bin/env python3
"""The exact 81-site Parts-inspired fixture, ordinary four-coloring."""
import argparse,json
from pathlib import Path
from itertools import combinations
from hashlib import sha256

DEN=7200
RAD=(-3,33,-15) # bitmask basis
ZERO=(0,)*8
E0=(1,)+(0,)*7
M=((-3)**(bool(i&1))*33**(bool(i&2))*(-15)**(bool(i&4)) for i in range(8))
FAC=tuple(M)

def add(x,y):return tuple(a+b for a,b in zip(x,y))
def sub(x,y):return tuple(a-b for a,b in zip(x,y))
def scale(x,n):return tuple(n*a for a in x)

def div(x,n):
    assert all(a%n==0 for a in x)
    return tuple(a//n for a in x)

def mul(x,y):
    z=[0]*8
    for i,a in enumerate(x):
        for j,b in enumerate(y):z[i^j]+=a*b*FAC[i&j]
    return tuple(z)

def bar(x):
    return tuple(-a if (i&5).bit_count()==1 else a for i,a in enumerate(x))

def norm(x):return mul(x,bar(x))

def norm_ind(x):
    # Real part in basis 1,sqrt(33),sqrt(5),sqrt(165);
    # imaginary part is sqrt(3) times a separate vector in the same basis.
    R=x[0],x[2],-3*x[5],-3*x[7]
    I=x[1],x[3],x[4],x[6]
    def sq(p):
        a,b,c,d=p
        return (a*a+33*b*b+5*c*c+165*d*d,2*a*b+10*c*d,
                2*a*c+66*b*d,2*a*d+2*b*c)
    return tuple(r+3*i for r,i in zip(sq(R),sq(I)))

def construct():
    u2=(1,1,0,0,0,0,0,0)
    s18=(15,0,0,1,0,0,0,0)
    r8=(7,0,0,0,1,0,0,0)
    tau50=(49,0,0,1,0,0,0,0)
    assert norm(s18)==scale(E0,18**2)
    assert norm(r8)==scale(E0,8**2)
    assert norm(tau50)==scale(E0,50**2)
    W={ZERO}
    p=E0
    for k in range(6):
        W.add(div(scale(p,2),2**k))
        p=mul(p,u2)
    assert p==scale(E0,64)
    Wdirect={(a,b,0,0,0,0,0,0) for a,b in
             [(0,0),(2,0),(1,1),(-1,1),(-2,0),(-1,-1),(1,-1)]}
    assert W==Wdirect and len(W)==7
    T2={add(a,b) for a in W for b in W}
    T={scale(p,DEN//2) for p in T2}
    S={div(scale(mul(p,s18),DEN),36) for p in T2}
    # Independent native lattice identity: A+B*omega coordinates in hex ball.
    Tind={(DEN*(2*a+b)//2,DEN*b//2,0,0,0,0,0,0)
          for a in range(-2,3) for b in range(-2,3) if abs(a+b)<=2}
    Sind={div(mul(p,s18),18) for p in Tind}
    assert len(T)==len(S)==19 and T==Tind and S==Sind and T&S=={ZERO}
    B=T|S
    rB={div(mul(p,r8),8) for p in B}
    assert B&rB=={ZERO} and len(B|rB)==73
    one={scale(E0,DEN*k) for k in range(3,6)}
    two={scale(tau50,(DEN//50)*k) for k in range(1,6)}
    assert len(one|two)==8 and not (one|two)&(B|rB)
    F=sorted(B|rB|one|two)
    assert len(F)==len(set(F))==81
    pos={q:i for i,q in enumerate(F)}
    def is_edge(x,y):assert norm(sub(x,y))==scale(E0,DEN**2)
    ref=[]
    for u in W-ZERO_SET:
        p=scale(u,DEN)
        q=div(mul(p,r8),8)
        assert p in B and q in rB and p!=q
        is_edge(p,q)
        ref.append(sorted([pos[p],pos[q]]))
    assert len(ref)==6
    e5=scale(E0,5*DEN),scale(tau50,5*(DEN//50))
    is_edge(*e5)
    four=tuple(div(scale(v,DEN),2) for v in ((1,1,0,0,0,0,0,0),(-1,1,0,0,0,0,0,0)))
    far=scale((0,1,0,0,0,0,0,0),DEN)
    rs=lambda p:div(mul(p,s18),18)
    spindle=(ZERO,far,rs(far),*four,*(rs(p) for p in four))
    assert len(set(spindle))==7 and set(spindle)<=set(F)
    for p in (*four,*(rs(q) for q in four)):is_edge(ZERO,p)
    is_edge(far,rs(far));is_edge(*four);is_edge(*(rs(q) for q in four))
    for p in four:is_edge(far,p);is_edge(rs(far),rs(p))
    H={'denominator':DEN,'generator_squares':RAD,'vertices':F,'ordinary_color_count':4,
       'marked_nonunit_pair_for_later':[pos[ZERO],pos[scale(E0,2*DEN)]],
       'reference_edges':sorted(ref),'tau_edge':sorted(pos[p] for p in e5),
       'spindle_vertices':[pos[p] for p in spindle]}
    return H

ZERO_SET={ZERO}

def all_edges(P):
    E=[]
    for i,j in combinations(range(len(P)),2):
        d=sub(P[i],P[j])
        q=norm(d)
        assert q[1]==q[3]==q[4]==q[6]==0
        k=(q[0],q[2],-3*q[5],-3*q[7])
        assert k==norm_ind(d)
        if q==scale(E0,DEN**2):E.append([i,j])
    return E

def cnf(n,E):
    v=lambda i,k:4*i+k+1
    for i in range(n):
        yield [v(i,k) for k in range(4)]
        for k,l in combinations(range(4),2):yield [-v(i,k),-v(i,l)]
    for a,b in E:
        for k in range(4):yield [-v(a,k),-v(b,k)]

def gen(out):
    H=construct()
    P=H['vertices']; n=len(P)
    H['unit_edges']=all_edges(P)
    E=H['unit_edges']
    assert all(e in E for e in H['reference_edges']) and H['tau_edge'] in E
    assert sorted(H['marked_nonunit_pair_for_later']) not in E
    out.mkdir(exist_ok=False)
    g=out/'exact-graph.json'
    g.write_text(json.dumps(H,separators=(',',':'))+'\n')
    lines=list(cnf(n,E))
    p=out/'ordinary-four.cnf'
    with p.open('w') as f:
        print('p cnf',4*n,len(lines),file=f)
        for row in lines:print(*row,0,file=f)
    r={'sites':n,'exact_pair_checks':n*(n-1)//2,'unit_edges':len(E),
       'reference_edges':H['reference_edges'],'tau_edge':H['tau_edge'],
       'graph_sha256':sha256(g.read_bytes()).hexdigest(),'cnf_sha256':sha256(p.read_bytes()).hexdigest()}
    (out/'generation.json').write_text(json.dumps(r,indent=2)+'\n')
    print(r)

def check(out,model):
    h=json.loads((out/'exact-graph.json').read_text())
    P=[tuple(p) for p in h['vertices']]
    assert P==construct()['vertices'] and len(P)==len(set(P))==81
    E={tuple(e) for e in h['unit_edges']}
    assert len(E)==len(h['unit_edges'])
    assert E=={(i,j) for i,j in combinations(range(len(P)),2)
               if norm_ind(sub(P[i],P[j]))==(DEN**2,0,0,0)}
    t=model.read_text().splitlines()
    assert [s for s in t if s.startswith('s ')]==['s SATISFIABLE']
    vs=[int(v) for s in t if s.startswith('v ') for v in s.split()[1:] if v!='0']
    assert sorted(map(abs,vs))==list(range(1,4*len(P)+1))
    values={abs(v):v>0 for v in vs}
    C=[]
    for a in range(len(P)):
        c=[k for k in range(4) if values[4*a+k+1]]
        assert len(c)==1
        C+=c
    assert all(C[a]!=C[b] for a,b in E)
    assert all(any(values[abs(l)]==(l>0) for l in c) for c in cnf(len(P),sorted(E)))
    a,b=h['marked_nonunit_pair_for_later']
    assert norm_ind(sub(P[a],P[b]))==(4*DEN**2,0,0,0)
    D=C.copy();D[a]=D[b]=4
    assert all(D[i]!=D[j] for i,j in E)
    (out/'checked-coloring.json').write_text(json.dumps({'ordinary_four':C,'marked_pair':[a,b],
        'equal_terminals_with_five':D},separators=(',',':'))+'\n')
    print(f'Independently audited all {len(E)} unit edges and complete proper four-coloring; verified a five-coloring with 0,2 equal.')

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('mode',choices=['generate','check'])
    p.add_argument('out',type=Path)
    p.add_argument('model',type=Path,nargs='?')
    a=p.parse_args()
    if a.mode=='generate':gen(a.out)
    else:check(a.out,a.model)

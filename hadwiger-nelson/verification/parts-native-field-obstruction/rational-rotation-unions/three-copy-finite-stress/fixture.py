#!/usr/bin/env python3
"""Exact, standard-library recipe for the three-copy fixture. No solver invocation."""
import argparse
import json
from collections import defaultdict
from fractions import Fraction as F
from hashlib import sha256
from itertools import combinations
from pathlib import Path

RAD=(-3,33,-7)
FAC=tuple(RAD[0]**bool(i&1)*RAD[1]**bool(i&2)*RAD[2]**bool(i&4)
          for i in range(8))

def q(a=0):
    return (F(a),)+(F(0),)*7

ZERO,ONE=q(),q(1)
s=(F(0),F(1))+(F(0),)*6
r=(F(0),F(0),F(1))+(F(0),)*5
j=(F(0),)*4+(F(1),)+(F(0),)*3

def add(x,y):
    return tuple(a+b for a,b in zip(x,y))

def sub(x,y):
    return tuple(a-b for a,b in zip(x,y))

def scale(x,a):
    return tuple(v*a for v in x)

def mul(x,y):
    z=[F(0)]*8
    for i,a in enumerate(x):
        if not a: continue
        for k,b in enumerate(y):
            if b: z[i^k]+=a*b*FAC[i&k]
    return tuple(z)

def bar(x):
    return tuple(-a if (i&5).bit_count()==1 else a for i,a in enumerate(x))

def norm(x):
    return mul(x,bar(x))

def norm_independent(x):
    # Basis 1,r,sqrt(21),r*sqrt(21) for the real part and for imag/sqrt(3).
    re=(x[0],x[2],-x[5],-x[7])
    im=(x[1],x[3],x[4]/3,x[6]/3)
    def square(y):
        a,b,c,d=y
        return (a*a+33*b*b+21*c*c+693*d*d,
                2*a*b+42*c*d,2*a*c+66*b*d,2*a*d+2*b*c)
    return tuple(a+3*b for a,b in zip(square(re),square(im)))

def reciprocal_s(x):
    assert not any(x[2:])
    n=x[0]**2+3*x[1]**2
    assert n
    y=scale(bar(x),1/n)
    assert mul(x,y)==ONE
    return y

def v2(a):
    if not a:return float('inf')
    n,d=abs(a.numerator),a.denominator
    return (n&-n).bit_length()-(d&-d).bit_length()

def local_s(x):
    assert not any(x[2:])
    # sqrt(-3)=1+2*eta, eta²+eta+1=0 at the 2-adic embedding.
    return x[0]+x[1],2*x[1]

def val_s(x):
    return min(map(v2,local_s(x)))

def residue_s(x):
    lo,hi=local_s(x)
    assert min(v2(lo),v2(hi))>=0
    return (lo.numerator&1)+2*(hi.numerator&1)

def construct():
    omega=scale(add(ONE,s),F(1,2))
    rho=scale(add(q(31),scale(j,3)),F(1,32))
    rho2=mul(rho,rho)
    sig=scale(add(q(15),mul(s,r)),F(1,18))
    assert norm(omega)==norm(rho)==norm(rho2)==norm(sig)==ONE
    assert add(rho,bar(rho))==q(F(31,16))
    assert add(rho2,bar(rho2))==q(F(449,256))
    assert rho2[0]==F(449,512) and rho2[4]==F(93,512)
    T,S=F(31,16),F(449,256)
    W={ZERO}
    z=ONE
    for _ in range(6):
        W.add(z);z=mul(z,omega)
    assert z==ONE and len(W)==7
    expected_w={(F(a,2),F(b,2))+(F(0),)*6 for a,b in
        [(0,0),(2,0),(1,1),(-1,1),(-2,0),(-1,-1),(1,-1)]}
    assert W==expected_w
    T2={add(x,y) for x in W for y in W}
    assert len(T2)==19
    mids=[scale(add(s,ONE),F(1,2)),scale(sub(s,ONE),F(1,2))]
    mids2=[mul(sig,m) for m in mids]
    far2=mul(sig,s)
    M={ZERO,s,far2,*mids,*mids2}
    D0=W|M
    core=T2|{q(3),q(4)}|D0
    assert len(M)==7 and len(D0)==11 and len(core)==24
    # Log every known Moser edge independently of the final norm scan.
    spindle=[(s,far2),tuple(mids),tuple(mids2)]
    spindle += [(ZERO,m) for m in mids+mids2]
    spindle += [(s,m) for m in mids]+[(far2,m) for m in mids2]
    assert all(norm(sub(a,b))==ONE for a,b in spindle)
    flats=[set(core) for _ in range(3)]
    flats[0]|={add(q(S),f) for f in D0}
    flats[1]|={add(q(T),f) for f in D0}
    p=scale(reciprocal_s(add(q(2),s)),F(16,3))
    u=mul(sub(q(2),s),reciprocal_s(add(q(2),s)))
    assert norm(p)==q(F(256,63)) and val_s(p)==4
    steps=[sig,mul(sig,u),bar(sig),mul(bar(sig),u),q(-1),scale(u,-1)]*2
    assert all(norm(d)==ONE for d in steps)
    z=ZERO
    for d in steps:
        z=add(z,d)
        flats[0].add(z);flats[2].add(z)
    assert z==p
    rots=[ONE,rho,rho2]
    lift=lambda k,x: mul(rots[k],x)
    bridges=[]
    groups=[defaultdict(set),{0:{lift(1,q(T))}},{0:{lift(2,ONE)}}]
    lower_wheel={add(q(S),w) for w in W}
    for x in lower_wheel:groups[0][residue_s(sub(x,q(S)))].add(x)
    edges_lower=set()
    for x,y in combinations(lower_wheel,2):
        if norm(sub(x,y))==ONE:
            a,b=(residue_s(sub(z,q(S))) for z in (x,y))
            edges_lower.add(tuple(sorted((a,b))))
    assert edges_lower==set(combinations(range(4),2))
    hits=defaultdict(set)
    for k,(A,B) in enumerate(((S+1,T),(S,F(1))),1):
        c=rots[k][0]
        D=1-c*c
        a0,t0=1/A,B/A
        u0=a0+t0-c
        h=4*k
        assert v2(c)==-h-1 and v2(t0)==h and v2(A)==-8
        for xi in (ZERO,ONE,omega,add(ONE,omega)):
            delta,b=scale(xi,-1/(A*A))[:2]
            ub=u0+delta
            assert v2(ub)==-h-1
            vr=(D-3*b*b)/ub
            a=(ub+vr)/2
            t=c+(ub-vr)/2
            assert a-a0-delta==-(delta*(delta+2*a0)+3*b*b)/(2*ub)
            assert v2(a-a0-delta)>=24+h
            Z=(a,b)+(F(0),)*6
            X=reciprocal_s(Z)
            Y=scale(X,t)
            assert norm(Z)==q(t*t-2*c*t+1)
            assert norm(sub(X,lift(k,Y)))==ONE
            assert val_s(X)==-8 and val_s(Y)==h-8
            assert residue_s(sub(X,add(q(A),xi)))==0
            assert val_s(sub(Y,q(B)))>=1
            if xi==ZERO:assert X==q(A) and Y==q(B)
            ci=residue_s(sub(X,q(S)))
            assert ci not in hits[k];hits[k].add(ci)
            flats[0].add(X);flats[k].add(Y)
            bridges.append((X,lift(k,Y)))
            groups[0][ci].add(X)
            groups[k][0].add(lift(k,Y))
    assert all(hits[k]==set(range(4)) for k in (1,2))
    xx,xp,yy,zz=q(S+1),q(S),lift(1,q(T)),lift(2,ONE)
    cycle=[(xx,yy),(yy,zz),(zz,xp),(xp,xx)]
    assert all(norm(sub(a,b))==ONE for a,b in cycle)
    shells=[(q(4),lift(1,q(4))),(lift(1,q(4)),lift(2,q(4))),(p,lift(2,p))]
    assert all(norm(sub(a,b))==ONE for a,b in shells)
    copies=[{lift(k,x) for x in fl} for k,fl in enumerate(flats)]
    assert all(copies[a]&copies[b]=={ZERO} for a,b in combinations(range(3),2))
    P=sorted(set().union(*copies))
    assert len(P)<=128
    pos={x:i for i,x in enumerate(P)}
    key=lambda e: sorted(pos[x] for x in e)
    role_groups={f'low_cell_{a}':sorted(pos[x] for x in groups[0][a]) for a in range(4)}
    role_groups['copy1_upper_T']=sorted(pos[x] for x in groups[1][0])
    role_groups['copy2_upper_1']=sorted(pos[x] for x in groups[2][0])
    meta={'sites':len(P),'copy_sizes_with_origin':list(map(len,copies)),
          'restricted_cell_groups':role_groups,'unit_cycle':list(map(key,cycle)),
          'positive_shell_edges':list(map(key,shells)),'bridge_edges':list(map(key,bridges)),
          'native_spindle_edges':list(map(key,spindle))}
    return P,meta

def all_edges(P, check_both=True):
    E=[]
    for a,b in combinations(range(len(P)),2):
        d=sub(P[a],P[b])
        n=norm_independent(d)
        if check_both:
            qn=norm(d)
            assert qn[1]==qn[3]==qn[4]==qn[6]==0
            assert (qn[0],qn[2],-qn[5],-qn[7])==n
        if n==(1,0,0,0):E.append([a,b])
    return E

def cnf(n,E):
    v=lambda i,k:5*i+k+1
    for i in range(n):
        yield [v(i,k) for k in range(5)]
        for k,l in combinations(range(5),2):yield [-v(i,k),-v(i,l)]
    for a,b in E:
        for k in range(5):yield [-v(a,k),-v(b,k)]

def generate(out):
    P,meta=construct(); E=all_edges(P)
    es={tuple(e) for e in E}
    for k in ('unit_cycle','positive_shell_edges','bridge_edges','native_spindle_edges'):
        assert all(tuple(e) in es for e in meta[k])
    out.mkdir(exist_ok=False)
    graph=out/'exact-graph.json'
    graph.write_text(json.dumps({'basis_squares':RAD,'coordinates':[[str(x) for x in p] for p in P],
                       'unit_edges':E,**meta},separators=(',',':'))+'\n')
    clauses=list(cnf(len(P),E))
    cp=out/'ordinary-five.cnf'
    with cp.open('w') as f:
        print('p cnf',5*len(P),len(clauses),file=f)
        for row in clauses:print(*row,0,file=f)
    print(json.dumps({'sites':len(P),'unit_edges':len(E),'complete_pair_checks':len(P)*(len(P)-1)//2,
           'graph_sha256':sha256(graph.read_bytes()).hexdigest(),
           'solver_input_sha256':sha256(cp.read_bytes()).hexdigest()},indent=2))

def check(out,model):
    lines=model.read_text().splitlines()
    assert [s for s in lines if s.startswith('s ')]==['s SATISFIABLE'], 'no positive model'
    data=json.loads((out/'exact-graph.json').read_text())
    P=[tuple(map(F,p)) for p in data['coordinates']]
    exact,meta=construct()
    assert P==exact and all(data[k]==v for k,v in meta.items())
    E=data['unit_edges']
    assert E==all_edges(P,False)
    literals=[int(x) for row in lines if row.startswith('v ') for x in row.split()[1:] if x!='0']
    assert sorted(map(abs,literals))==list(range(1,5*len(P)+1))
    by_abs={abs(x):x>0 for x in literals}
    colors=[]
    for i in range(len(P)):
        cs=[k for k in range(5) if by_abs[5*i+k+1]]
        assert len(cs)==1
        colors+=cs
    assert all(colors[i]!=colors[j] for i,j in E)
    assert all(any(by_abs[abs(l)]==(l>0) for l in clause) for clause in cnf(len(P),E))
    split={k:sorted({colors[i] for i in ids}) for k,ids in data['restricted_cell_groups'].items()
           if len({colors[i] for i in ids})>1}
    assert split, 'A model must break at least one of the six restricted cell classes'
    (out/'checked-positive.json').write_text(json.dumps({'colors':colors,'split_cells':split},
                                                   separators=(',',':'))+'\n')
    print(f'checked positive witness on all {len(E)} edges; split cells {split}')

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('mode',choices=('generate','check'))
    p.add_argument('out',type=Path)
    p.add_argument('model',type=Path,nargs='?')
    a=p.parse_args()
    if a.mode=='generate':
        assert a.model is None
        generate(a.out)
    else:
        assert a.model is not None
        check(a.out,a.model)

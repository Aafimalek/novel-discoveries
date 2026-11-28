#!/usr/bin/env python3
"""Exact 88-point control and nonzero rational-B polynomial audits."""
import argparse,importlib.util,json
from collections import Counter
from fractions import Fraction as F
from functools import reduce
from hashlib import sha256
from itertools import combinations,product
from math import gcd,lcm
from pathlib import Path
PINS={
'fixture':'dbfa98684962ca65a1dd5302f002b60999b4b1d7d58a4e753c018f3559592a5f',
'local':'7d25911e7740b8ce2ddf9846d3f11562611fb73f30b7b4825f388012a01a49ec',
'pole':'a08579e99ecbb839d064b8c790950296524ee35df96569b50fb8b309608b432e',
'graph24':'369fcee0d688701326668e7c7c13f06af89b8c48c5e91107ccbb10e5f28f9fc7',
'samples':'9f85ff8cf8006e0c41210a452ac7b8da119951d7a42feb77af63c86f021fa5e5'
}
KVALS=(2,22,722,472,16722,4222)
FAC=tuple((-3)**bool(i&1)*33**bool(i&2)*(-7)**bool(i&4) for i in range(8))
Ibar=tuple((-1 if (i&5).bit_count()==1 else 1) for i in range(8))
Re=(0,2,5,7)
def sha(p):return sha256(p.read_bytes()).hexdigest()
def pin(p,k):
    assert sha(p)==PINS[k],p
    return p
def module(p,k):
    spec=importlib.util.spec_from_file_location('fourpatch_'+k,pin(p,k))
    m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
    return m
def read(p,k):
    return json.loads(pin(p,k).read_text())
def text(x):return [str(q) for q in x]

def sub(a,b):return tuple(x-y for x,y in zip(a,b))
def add(a,b):return tuple(x+y for x,y in zip(a,b))
def mreal(a,b,twice=False):
    # (a·conj(b)) restricted to real coefficients, optionally twice.
    o=[0]*8
    for i,x in enumerate(a):
        if not x:continue
        for j in Re:
            k=i^j
            if b[k]:o[j]+=x*b[k]*Ibar[k]*FAC[i&k]
    w=2 if twice else 1
    return tuple(w*o[i] for i in Re)
def poly_norm(X):
    a,b,c=X
    return (mreal(a,a),mreal(a,b,True),add(mreal(b,b),mreal(a,c,True)),
            mreal(b,c,True),mreal(c,c))
def primitive(p):
    p=list(p)
    while p and not p[-1]:p.pop()
    if not p:return ()
    g=reduce(gcd,p,0)
    if p[-1]<0:g=-g
    return tuple(x//g for x in p)
def rem(a,b):
    while a and len(a)>=len(b):
        z=a[-1];w=b[-1];h=len(a)-len(b)
        a=primitive([w*x-(z*b[i-h] if i>=h else 0) for i,x in enumerate(a)])
    return a
def gcdp(a,b):
    while b:a,b=b,rem(a,b)
    return a
def gcd_rows(poly):
    # Remove powers of B only because this audit addresses B != 0.
    g=()
    for row in zip(*poly):
        k=next((i for i,x in enumerate(row) if x),None)
        if k is None:continue
        q=primitive(row[k:])
        if len(q)==1:return (1,)
        g=gcdp(g,q)
        if len(g)==1:return g
    return g
def classify(row,tang):
    if not row:return 'identity'
    if row==(1,):return 'constant'
    assert row==tang,(row,tang)
    return 'nonrational_quadratic'

def symbols(m,k):
    C=F(63,1024);c=F(31,32);T=2*c;u0=F(63,992)
    U=(m.q(u0),m.scale(m.r,k),m.ZERO)
    U2=(m.q(u0*u0),m.scale(m.r,2*u0*k),m.q(33*k*k))
    D=(m.add(U2[0],m.q(C)),m.add(U2[1],m.scale(m.s,2*u0)),
       m.add(m.sub(U2[2],m.q(3)),m.scale(m.mul(m.r,m.s),2*k)))
    X=tuple(m.scale(a,2) for a in U)
    Y=(m.add(m.scale(U[0],T),m.sub(U2[0],m.q(C))),
       m.add(m.scale(U[1],T),U2[1]),m.add(U2[2],m.q(3)))
    Z=tuple(m.sub(m.scale(y,T),x) for x,y in zip(X,Y))
    return D,(Y,X,Z,Y)
def ev(m,P,B):
    return m.add(P[0],m.add(m.scale(P[1],B),m.scale(P[2],B*B)))
def native_inverse(m,nf,x):
    a,b=nf.rational_form(m.norm(x))
    ra,rb=nf.realinv(a,b)
    return m.mul(m.bar(x),m.add(m.q(ra),m.scale(m.r,rb)))

def prepare(m,nf,po,P24,samples):
    S=samples[0]
    assert S['depth']==1 and S['k']==2 and S['ell']==1
    B=F(512,25)
    D,NN=symbols(m,2)
    inv=native_inverse(m,nf,ev(m,D,B))
    Y,X,Z,_=[m.mul(ev(m,a,B),inv) for a in NN]
    assert X==tuple(map(F,S['native_x'])) and Y==tuple(map(F,S['native_y']))
    assert Z==m.sub(m.scale(Y,F(31,16)),X)
    assert nf.nativeval(Z)==11 and po.min5(nf,Z)==-1
    rho=m.scale(m.add(m.q(31),m.scale(m.j,3)),F(1,32))
    rho2=m.mul(rho,rho)
    rots=[m.ONE,rho,rho,rho2]
    P=[tuple(map(F,t)) for t in P24['coordinates']]
    assert P24['unit_edges']==m.all_edges(P) and len(P)==24
    assert all(P24['proper_five_colors'][i]!=P24['proper_five_colors'][j] for i,j in P24['unit_edges'])
    offsets=[m.sub(m.mul(m.bar(rho),q),X) for q,c in zip(P,P24['proper_five_colors']) if c!=4]
    assert offsets[10]==m.ZERO and len(set(offsets))==22
    omega=m.scale(m.add(m.ONE,m.s),F(1,2))
    W={m.ZERO};w=m.ONE
    for _ in range(6):W.add(w);w=m.mul(w,omega)
    sig=m.scale(m.add(m.q(15),m.mul(m.r,m.s)),F(1,18))
    mids=[m.scale(m.add(m.s,m.ONE),F(1,2)),m.scale(m.sub(m.s,m.ONE),F(1,2))]
    M=[m.ZERO,m.s,m.mul(sig,m.s),*mids,*(m.mul(sig,v) for v in mids)]
    assert len(set(M))==7 and set(offsets)==({m.add(a,b) for a in W for b in W}|set(M))
    assert {Y,m.mul(rho2,Y)}=={q for q,c in zip(P,P24['proper_five_colors']) if c==4}
    centers=[m.mul(r,a) for r,a in zip(rots,(Y,X,Z,Y))]
    assert m.add(centers[0],centers[3])==m.add(centers[1],centers[2])
    assert m.norm(m.sub(centers[0],centers[3]))!=m.ONE
    assert m.norm(m.sub(centers[1],centers[2]))!=m.ONE
    d1=m.sub(centers[1],centers[0]);d2=m.sub(centers[1],centers[3])
    assert m.norm(d1)==m.norm(d2)==m.ONE and po.min5(nf,d1)==po.min5(nf,d2)==-1
    assert po.min5(nf,m.mul(d1,m.bar(d2)))>=0
    assert po.min5(nf,m.mul(d1,m.bar(rho)))<0
    return offsets,rots,(Y,X,Z,Y),M

def audit(m,P,rots,k):
    D,A=symbols(m,k)
    Pn=[
        tuple(m.mul(rt,m.add(m.mul(d,p),a)) for d,a in zip(D,an))
        for rt,an in zip(rots,A) for p in P
    ]
    L=lcm(*(v.denominator for Poly in (*Pn,D) for q in Poly for v in q))
    pack=lambda X:tuple(tuple(int(v*L) for v in q) for q in X)
    Ns=list(map(pack,Pn));normD=poly_norm(pack(D))
    tang=primitive((-21,0,961*(11*k*k+1)))
    U=Counter();V=Counter();pairs=[]
    for i,j in combinations(range(88),2):
        if i//22==j//22:continue
        N=tuple(sub(a,b) for a,b in zip(Ns[i],Ns[j]))
        un=tuple(sub(a,b) for a,b in zip(poly_norm(N),normD))
        u=classify(gcd_rows(un),tang)
        v=classify(gcd_rows(N),tang)
        U[u]+=1;V[v]+=1
        pairs.append([i,j,u,v])
        if u=='nonrational_quadratic' or v=='nonrational_quadratic':
            assert i//22==1 and j//22==2
    assert len(pairs)==2904
    assert U=={'identity':4,'constant':2804,'nonrational_quadratic':96}
    assert V=={'constant':2882,'nonrational_quadratic':22}
    ids=[v[:2] for v in pairs if v[2]=='identity']
    assert ids==[[10,32],[10,54],[32,76],[54,76]]
    assert (11*k*k+1)%11==1 and 21%11==10 and 10 not in {k*k%11 for k in range(11)}
    return {'k':k,'primitive_exceptional_gcd':list(tang),'unit':dict(U),
            'coincidence':dict(V),'unit_identities':ids,'rows':pairs}

def main():
    p=argparse.ArgumentParser(description=__doc__)
    for k in ('fixture','local','pole','graph24','samples','out'):p.add_argument(k,type=Path)
    a=p.parse_args()
    m=module(a.fixture,'fixture');nf=module(a.local,'local');po=module(a.pole,'pole')
    P,rots,A,M=prepare(m,nf,po,read(a.graph24,'graph24'),read(a.samples,'samples'))
    Q=[m.mul(r,m.add(c,p)) for r,c in zip(rots,A) for p in P]
    assert len(Q)==len(set(Q))==88
    E=m.all_edges(Q)
    assert E==m.all_edges(Q,False) and len(E)==196
    assert [sum(i//22==j//22==k for i,j in E) for k in range(4)]==[48]*4
    between=[e for e in E if e[0]//22!=e[1]//22]
    assert between==[[10,32],[10,54],[32,76],[54,76]]
    C=[po.residue(nf,p)^(int(k in (1,2))) for k in range(4) for p in P]
    assert len(set(C))==4 and all(C[i]!=C[j] for i,j in E)
    MI=[P.index(t) for t in M]
    mE=[(i,j) for i,j in combinations(range(7),2) if
        sorted((MI[i],MI[j])) in E]
    assert len(MI)==len(set(MI))==7 and len(mE)==11
    tries=0
    for c in product(range(3),repeat=6):
        q=(0,*c)
        assert any(q[i]==q[j] for i,j in mE)
        tries+=1
    assert tries==729
    aud=[audit(m,P,rots,k) for k in KVALS]
    a.out.mkdir(exist_ok=False)
    (a.out/'exact-88.json').write_text(json.dumps({'basis_squares':[-3,33,-7],
        'coordinates':list(map(text,Q)),'unit_edges':E,'four_colors':C,
        'spindle_ids':MI,'spindle_edges_local':mE,'center_indices':[10,32,54,76]},
        separators=(',',':'))+'\n')
    (a.out/'pairwise-polynomials.json').write_text(json.dumps(aud,separators=(',',':'))+'\n')
    stats={'vertices':88,'unit_edges':196,'checked_full_pairs':3828,'patch_edge_counts':[48]*4,
           'cross_edges':between,'four_color_sizes':[Counter(C)[i] for i in range(4)],
           'spindle_three_color_assignments_checked':tries,'fixed_k':list(KVALS),
           'polynomial_pairs_per_k':2904,'total_polynomial_pairs':6*2904,
           'unit_identity_constant_quadratic':[4,2804,96],
           'coincidence_identity_constant_quadratic':[0,2882,22],
           'sha256':{f.name:sha(f) for f in sorted(a.out.iterdir())}}
    (a.out/'summary.json').write_text(json.dumps(stats,indent=2)+'\n')
    print(json.dumps(stats,indent=2))

if __name__=='__main__':main()

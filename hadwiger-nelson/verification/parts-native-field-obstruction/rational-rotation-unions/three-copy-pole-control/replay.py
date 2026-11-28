#!/usr/bin/env python3
"""Exact pole-depth audit and 24-point five-colored control; no solver."""
import argparse,importlib.util,json
from collections import Counter
from fractions import Fraction as F
from hashlib import sha256
from itertools import combinations
from math import gcd
from pathlib import Path

PINS={
  'fixture':'dbfa98684962ca65a1dd5302f002b60999b4b1d7d58a4e753c018f3559592a5f',
  'saturation':'7d25911e7740b8ce2ddf9846d3f11562611fb73f30b7b4825f388012a01a49ec'
}
DEPTH_K=((1,2),(2,22),(3,722),(4,472),(5,16722),(6,4222))

def file_sha(p):return sha256(p.read_bytes()).hexdigest()
def module(path,label):
    assert file_sha(path)==PINS[label],path
    spec=importlib.util.spec_from_file_location('pole_'+label,path)
    m=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m
def text(q):return [str(a) for a in q]

def ratio5(n):
    # s_5/r=theta, 11*theta²+1=0, theta≡2 mod5.
    t=2
    for i in range(1,n):
        q=5**i
        lifts=[t+k*q for k in range(5) if (11*(t+k*q)**2+1)%(5*q)==0]
        assert len(lifts)==1
        t=lifts[0]
    assert (11*t*t+1)%5**n==0
    return t

def local5(nf,Q,sgn):
    # In split factor, A+B s -> A+sgn*B theta r.
    assert sgn in (-1,1) and not any(Q[4:])
    a,b,c,d=Q[:4]
    if not (b or d):return min(nf.vv(a,5),nf.vv(c,5))
    k0=min(nf.vv(b,5),nf.vv(d,5))
    n=8
    while n<=512:
        v=ratio5(n)
        red=(a+sgn*33*d*v,c+sgn*b*v)
        e=min(nf.vv(q,5) for q in red)
        if e<n+k0:return e
        n*=2
    raise AssertionError('5-adic split accuracy')

def min5(nf,Q):
    return min(nf.vv(a,5) for a in Q)
def red2(nf,a,b):
    if b:
        n=max(2,1-nf.vv(b,2))
        a+=b*nf.sqrt33(n)
    assert nf.vv(a,2)>=0
    return a.numerator%2
def residue(nf,Q):
    assert not any(Q[4:])
    a,b,c,d=Q[:4]
    return red2(nf,a+b,c+d)+2*red2(nf,2*b,2*d)

def calculate(m,nf,depth,k,ell,params):
    rho,rho2,c,D,U0,T=params
    assert depth>=1 and k%2==0 and k%5==2 and gcd(ell,10)==1
    assert nf.vv(F(11*k*k+1),5)==depth
    B=F(512,5**(2*depth)*ell)
    U=m.add(m.q(U0),m.scale(m.r,k*B))
    V=m.scale(m.add(m.q(U[0]),m.scale(m.r,-U[2])),
              (D-3*B*B)/(U[0]*U[0]-33*U[2]*U[2]))
    A=m.scale(m.add(U,V),F(1,2))
    t=m.add(m.q(c),m.scale(m.sub(U,V),F(1,2)))
    Z=m.add(A,m.scale(m.s,B))
    n0,n1=nf.rational_form(m.norm(Z))
    w0,w1=nf.realinv(n0,n1)
    x=m.mul(m.bar(Z),m.add(m.q(w0),m.scale(m.r,w1)))
    y=m.mul(t,x)
    assert m.mul(x,Z)==m.ONE
    assert m.norm(Z)==m.add(m.q(1),m.sub(m.mul(t,t),m.scale(t,2*c)))
    assert nf.nativeval(x)==-4 and nf.nativeval(y)==0
    dx=nf.nativeval(m.sub(x,m.q(T)))
    dy=nf.nativeval(m.sub(y,m.ONE))
    assert dx>=1 and dy>=5
    actual=(m.mul(rho,x),y,m.mul(rho2,y))
    d1,d2=[m.sub(actual[0],q) for q in actual[1:]]
    assert all(m.norm(d)==m.ONE and m.norm_independent(d)==(1,0,0,0) for d in (d1,d2))
    assert m.norm(m.sub(*actual[1:]))!=m.ONE
    vals=[min5(nf,q) for q in (*actual,d1,d2)]
    assert vals==[0,-depth,-depth,-depth,-depth]
    assert [local5(nf,Z,sgn) for sgn in (-1,1)]==[0,-2*depth]
    assert [local5(nf,x,sgn) for sgn in (-1,1)]==[0,2*depth]
    assert [local5(nf,y,sgn) for sgn in (-1,1)]==[-depth,depth]
    assert [local5(nf,t,sgn) for sgn in (-1,1)]==[-depth,-depth]
    xmarks=[x,m.mul(rho,x),m.mul(rho2,x)]
    ymarks=[y,m.mul(rho,y),m.mul(rho2,y)]
    six=xmarks+ymarks
    assert len(set(six))==6
    # Two symmetry stars, not a new coupling. Audit all marked pairs.
    got={(i,j) for i,j in combinations(range(6),2) if m.norm(m.sub(six[i],six[j]))==m.ONE}
    assert got=={(1,3),(1,5),(0,4),(2,4)}
    assert all(min5(nf,m.sub(six[i],six[j]))==-depth for i,j in got)
    rec={'depth':depth,'k':k,'ell':ell,'native_x':text(x),'native_y':text(y),
         'native_t':text(t),'native_Z':text(Z),'center_and_outer':list(map(text,actual)),
         'coeff_valuations_center_outer_displacements':vals,
         'Z_split_5_valuations':[0,-2*depth],'x_split_5_valuations':[0,2*depth],
         'y_split_5_valuations':[-depth,depth],'t_5_valuation':-depth,
         'native_2_valuations':[-4,0],'native_2_nearness':[dx,dy],
         'edges_in_x0_x1_x2_y0_y1_y2':sorted(got)}
    return rec,x,y

def control(m,nf,x,y,params):
    rho,rho2,c,D,U0,T=params
    w=m.scale(m.add(m.ONE,m.s),F(1,2))
    sig=m.scale(m.add(m.q(15),m.mul(m.s,m.r)),F(1,18))
    W={m.ZERO};p=m.ONE
    for _ in range(6):W.add(p);p=m.mul(p,w)
    assert p==m.ONE and len(W)==7
    mids=[m.scale(m.add(m.s,m.ONE),F(1,2)),m.scale(m.sub(m.s,m.ONE),F(1,2))]
    M={m.ZERO,m.s,m.mul(sig,m.s),*mids,*(m.mul(sig,d) for d in mids)}
    patch={m.add(p,q) for p in W for q in W}|M
    assert len(patch)==22
    space={m.mul(rho,m.add(x,u)):residue(nf,u) for u in patch}
    R=(m.ONE,rho2)
    for a in R:
        q=m.mul(a,y)
        assert q not in space
        space[q]=4
    tests=[]
    for u in sorted(patch):
        X=m.add(x,u)
        assert nf.nativeval(X)==-4
        n0,n1=nf.rational_form(m.norm(X))
        d0,d1=nf.realinv(n0,n1);dg=(d0-D,d1)
        roots=nf.roots(*dg)
        for j,Rj in zip((0,2),R):
            rec={'dest_copy':j,'native_source':text(X),'discriminant':list(map(str,dg)),
                 'higher_native_dest':None}
            if roots:
                ts=[(a+c,b) for a,b in roots]
                assert sorted(nf.realval(*t) for t in ts)==[-4,4]
                a,b=next(t for t in ts if nf.realval(*t)==4)
                Y=m.mul(X,m.add(m.q(a),m.scale(m.r,b)))
                assert X==x and Y==y
                assert m.norm(m.sub(m.mul(rho,X),m.mul(Rj,Y)))==m.ONE
                rec['higher_native_dest']=text(Y)
            tests.append(rec)
    assert len(tests)==44 and sum(t['higher_native_dest'] is not None for t in tests)==2
    P=sorted(space);E=m.all_edges(P);C=[space[x] for x in P]
    assert len(P)==24 and E==m.all_edges(P,False) and len(E)==50
    assert all(C[i]!=C[j] for i,j in E)
    return {'basis_squares':[-3,33,-7],'coordinates':list(map(text,P)),
            'unit_edges':E,'proper_five_colors':C},tests

def main():
    p=argparse.ArgumentParser(description=__doc__)
    for name in ('fixture','saturation','out'):p.add_argument(name,type=Path)
    a=p.parse_args()
    m=module(a.fixture,'fixture');nf=module(a.saturation,'saturation')
    rho=m.scale(m.add(m.q(31),m.scale(m.j,3)),F(1,32))
    rho2=m.mul(rho,rho)
    c=F(31,32);D=1-c*c;T=2*c;U0=2/T-c
    assert U0==F(63,992) and D==F(63,1024)
    assert m.norm(rho)==m.norm(rho2)==m.ONE
    params=(rho,rho2,c,D,U0,T)
    data=[]
    for depth,k in DEPTH_K:
        for ell in (1,101):
            row,x,y=calculate(m,nf,depth,k,ell,params)
            if depth==ell==1:
                assert row['native_2_nearness']==[1,5]
                G,tests=control(m,nf,x,y,params)
            data.append(row)
    assert len(data)==12
    a.out.mkdir(exist_ok=False)
    for name,obj in [('samples.json',data),('exact-24.json',G),('saturation-44.json',tests)]:
        (a.out/name).write_text(json.dumps(obj,separators=(',',':'))+'\n')
    stats={'sample_depths':list(range(1,7)),'ell_values':[1,101],'sample_count':len(data),
           'control_sites':len(G['coordinates']),'control_unit_edges':len(G['unit_edges']),
           'control_full_pair_checks':len(G['coordinates'])*(len(G['coordinates'])-1)//2,
           'control_saturation_tests':len(tests),'control_higher_attachments':2,
           'control_colors':[Counter(G['proper_five_colors'])[i] for i in range(5)],
           'sha256':{f.name:file_sha(f) for f in sorted(a.out.iterdir())}}
    (a.out/'summary.json').write_text(json.dumps(stats,indent=2)+'\n')
    print(json.dumps(stats,indent=2))

if __name__=='__main__':main()

#!/usr/bin/env python3
"""Solver-free exact one-pass patch saturation and finite-field coloring."""
import argparse, importlib.util, json
from collections import Counter
from fractions import Fraction as F
from hashlib import sha256
from itertools import combinations, product
from math import isqrt
from pathlib import Path

PSRC='dbfa98684962ca65a1dd5302f002b60999b4b1d7d58a4e753c018f3559592a5f'
PGRAPH='32e1f361f4b473c3eda5cc505be44405d6c01860ee0646e585eb129e150352b4'

def digest(bytes_):
    return sha256(bytes_).hexdigest()
def load(path, pin):
    raw=path.read_bytes()
    assert digest(raw)==pin,path
    return raw
def import_source(path):
    load(path,PSRC)
    spec=importlib.util.spec_from_file_location('pinned_stress_fixture',path)
    m=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m
def frac_sqrt(x):
    if x<0:return None
    a,b=isqrt(x.numerator),isqrt(x.denominator)
    return F(a,b) if a*a==x.numerator and b*b==x.denominator else None
def square(a,b):
    return a*a+33*b*b,2*a*b
def roots(a,b):
    out=set()
    def accept(u,v):
        assert square(u,v)==(a,b)
        out.update(((u,v),(-u,-v)))
    if not b:
        u,v=frac_sqrt(a),frac_sqrt(a/33)
        if u is not None:accept(u,F(0))
        if v is not None:accept(F(0),v)
    else:
        w=frac_sqrt(a*a-33*b*b)
        if w is not None:
            for t in (w,-w):
                u=frac_sqrt((a+t)/2)
                if u:accept(u,b/(2*u))
    assert len(out)<=2
    return sorted(out)
def vv(q,p):
    if not q:return float('inf')
    a,b=abs(q.numerator),q.denominator
    k=0
    while a%p==0:a//=p;k+=1
    while b%p==0:b//=p;k-=1
    return k
def sqrt33(n):
    assert n>=2
    r=1
    for k in range(2,n):
        if (r*r-33)%(1<<(k+2)):r+=1<<k
        assert (r*r-33)%(1<<(k+2))==0
    assert 0<=r<1<<n and r%4==1
    return r
def realval(a,b):
    if not b:return vv(a,2)
    n=8
    while n<=2048:
        r=sqrt33(n)
        v=vv(a+b*r,2)
        if v<n+vv(b,2):return v
        n*=2
    raise AssertionError('insufficient binary accuracy')
def nativeval(x):
    assert not any(x[4:])
    return min(realval(x[0]+x[1],x[2]+x[3]), 1+realval(x[1],x[3]))
def realinv(a,b):
    n=a*a-33*b*b
    assert n
    return a/n,-b/n
def enc(q):
    return [str(a) for a in q]
def rational_form(x):
    assert not (x[1] or x[3] or any(x[4:]))
    return x[0],x[2]
def f25mul(x,y):
    a,b=x;c,d=y
    return ((a*c+3*b*d)%5,(a*d+b*c)%5)
def finite_directions():
    U=[]
    for a,b,c,d in product(range(5),repeat=4):
        u,v=f25mul((a,b),(a,b)),f25mul((c,d),(c,d))
        if ((u[0]+v[0])%5,(u[1]+v[1])%5)==(1,0):
            assert (a+c+2*d)%5
            U.append([a,b,c,d])
    assert len(U)==24
    return U
def red(x):
    assert x.denominator%5
    return x.numerator*pow(x.denominator,-1,5)%5
def rho5vec(q):
    return tuple(red(x) for x in (q[0]-q[5],q[2]-q[7],3*q[3]+q[6],q[1]+q[4]/3))
def color(q):
    a,b,c,d=rho5vec(q)
    return (a+c+2*d)%5

def main():
    p=argparse.ArgumentParser(description=__doc__)
    for a in ('base_source','base_graph','output'):p.add_argument(a,type=Path)
    a=p.parse_args();m=import_source(a.base_source)
    old=json.loads(load(a.base_graph,PGRAPH))
    P0=[tuple(map(F,z)) for z in old['coordinates']]
    rebuild,meta=m.construct()
    assert P0==rebuild and len(P0)==len(set(P0))==128
    assert old['unit_edges']==m.all_edges(P0)==m.all_edges(P0,False) and len(old['unit_edges'])==229
    assert all(old[k]==v for k,v in meta.items())
    s,r,j=m.s,m.r,m.j
    W={m.add(m.q(x/2),m.scale(s,y/2)) for x,y in
        [(F(0),F(0)),(F(2),F(0)),(F(1),F(1)),(F(-1),F(1)),
         (F(-2),F(0)),(F(-1),F(-1)),(F(1),F(-1))]}
    sig=m.scale(m.add(m.q(15),m.mul(s,r)),F(1,18))
    rho=m.scale(m.add(m.q(31),m.scale(j,3)),F(1,32))
    R=[m.ONE,rho,m.mul(rho,rho)]
    d0=m.scale(m.add(s,m.ONE),F(1,2)); d1=m.scale(m.sub(s,m.ONE),F(1,2))
    M={m.ZERO,s,m.mul(sig,s), d0,d1,m.mul(sig,d0),m.mul(sig,d1)}
    patch={m.add(x,y) for x in W for y in W}|M
    assert len(W)==7 and len(M)==7 and len(patch)==22
    centers=(F(449,256),F(31,16))
    original=set(P0); coords=set(P0); lift=lambda i,x:m.mul(R[i],x)
    tests=[];attachments=[];hist=Counter()
    for i,C in enumerate(centers):
        for x in sorted(patch):
            X=m.add(m.q(C),x)
            near=lift(i,X); coords.add(near)
            va=nativeval(X);assert va==-8+4*i
            n0,n1=rational_form(m.norm(X))
            inv0,inv1=realinv(n0,n1)
            vn=realval(n0,n1)
            assert vn==2*va
            for j in range(3):
                if j==i:continue
                k=abs(i-j); c=R[k][0]; h=4*k
                D=(inv0+c*c-1,inv1)
                srts=roots(*D)
                record={'from_copy':i,'to_copy':j,'native_source':enc(X),
                        'discriminant':list(map(str,D)),'higher_native_dest':None,
                        'already_in_original':None}
                if srts:
                    possible={(c+u,v) for u,v in srts}
                    assert sorted(realval(u,v) for u,v in possible)==[-h,h]
                    t=next((q for q in possible if realval(*q)==h))
                    t=m.add(m.q(t[0]),m.scale(r,t[1]))
                    Y=m.mul(X,t)
                    assert nativeval(Y)==va+h
                    destination=lift(j,Y)
                    assert m.norm(m.sub(near,destination))==m.ONE
                    assert m.norm_independent(m.sub(near,destination))==(1,0,0,0)
                    record.update(higher_native_dest=enc(Y),already_in_original=destination in original)
                    attachments.append((i,X,j,Y)); hist[(i,X)]+=1; coords.add(destination)
                tests.append(record)
    exp={(0,m.q(F(449,256)),2,m.ONE),
         (0,m.q(F(705,256)),1,m.q(F(31,16))),
         (1,m.q(F(31,16)),0,m.ONE),(1,m.q(F(31,16)),2,m.ONE)}
    assert len(tests)==88 and len(attachments)==len(exp)==4 and set(attachments)==exp
    assert all(t['already_in_original'] for t in tests if t['higher_native_dest'] is not None)
    assert {k for k,n in hist.items() if n==2}=={(1,m.q(F(31,16)))}
    P=sorted(coords)
    assert len(P)==150 and len(coords-original)==22
    E=m.all_edges(P)
    assert E==m.all_edges(P,False) and len(E)==285
    assert all(t.denominator%5 for x in P for t in x)
    U=finite_directions(); Uset=set(map(tuple,U))
    C=[color(x) for x in P]
    assert Counter(C)==dict(enumerate((27,29,36,29,29)))
    for i,j in E:
        assert rho5vec(m.sub(P[i],P[j])) in Uset
        assert C[i]!=C[j]
    # A unit outside the coefficient-integral displacement screen; not a cross attachment.
    outside=m.scale(m.add(m.q(-49),m.mul(s,r)),F(1,50))
    assert m.norm(outside)==m.ONE and outside[0].denominator%5==0
    # The two factors over 5 are not the same as coefficient-wise integrality.
    # x=(sqrt(33)-2sqrt(-3))²=21-4sqrt(33)sqrt(-3) is primitive in that basis,
    # yet its absolute field norm to Q(sqrt(33)) has valuation 2.
    cancel=m.mul(m.sub(r,m.scale(s,2)),m.sub(r,m.scale(s,2)))
    assert cancel==m.sub(m.q(21),m.scale(m.mul(r,s),4))
    assert m.norm(cancel)==m.q(2025) and vv(m.norm(cancel)[0],5)==2
    a.output.mkdir(exist_ok=False)
    pos={x:i for i,x in enumerate(P)}
    graph={'basis_squares':[-3,33,-7],'coordinates':[enc(x) for x in P],'unit_edges':E,
           'original_ids':sorted(pos[x] for x in P0),'proper_five_colors':C}
    (a.output/'exact-150.json').write_text(json.dumps(graph,separators=(',',':'))+'\n')
    (a.output/'saturation-88.json').write_text(json.dumps(tests,indent=2)+'\n')
    (a.output/'mod5-unit-directions.json').write_text(json.dumps(U,separators=(',',':'))+'\n')
    r={'original_vertices':128,'original_unit_edges':229,'final_vertices':len(P),'final_unit_edges':len(E),
       'full_final_unordered_pairs':len(P)*(len(P)-1)//2,'saturation_tests':len(tests),
       'higher_attachments':len(attachments),'new_attachment_destinations':0,'added_patch_vertices':22,
       'mod5_unit_directions':len(U),'color_sizes':list(dict(sorted(Counter(C).items())).values()),
       'sha256':{f.name:digest(f.read_bytes()) for f in sorted(a.output.iterdir())}}
    (a.output/'summary.json').write_text(json.dumps(r,indent=2)+'\n')
    print(json.dumps(r,indent=2))

if __name__=='__main__':main()

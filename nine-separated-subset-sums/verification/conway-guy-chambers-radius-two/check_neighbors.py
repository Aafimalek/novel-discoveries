"""Exact signed-inequality and positive-dual replay. No optimizer."""
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import argparse

A=(77,117,137,148,154,157,159,160,161)
Y=(1,1,2,4,8,15,25,48,57)
NAMES=('++++.-.--','-++++-.--','.-+++..--','..-+++.--','...-+++--',
       '....-++.-','.....-++-','......-+.','.......-+')
EXTRAS=('----..+++','+----.+++','.+----+++')
CODE={'+':1,'.':0,'-':-1}
DECODE={v:k for k,v in CODE.items()}
OBJ=(0,)*8+(1,)

def word(w): return tuple(CODE[c] for c in w)
def signs(v): return ''.join(DECODE[c] for c in v)
def dot(x,y): return sum(a*b for a,b in zip(x,y))
def plus(*vs): return tuple(sum(h) for h in zip(*vs))
def times(k,r): return tuple(k*x for x in r)
def full_model(flip,ors):
    return tuple(times(-1,u) if u==flip else u for u in ors)

def primal_ok(x, model):
    assert len(x)==9 and 0<x[0]<x[1]<x[2]<x[3]<x[4]<x[5]<x[6]<x[7]<x[8]
    assert all(dot(u,x)>=1 for u in model)
    sums=sorted(sum(x[i] for i in range(9) if (mask>>i)&1) for mask in range(512))
    assert len(set(sums))==512 and all(y-x>=1 for x,y in zip(sums,sums[1:]))

def dual_ok(terms,model):
    allowed=set(model)
    assert all(c>=0 and r in allowed for c,r in terms)
    assert plus(*(times(c,r) for c,r in terms))==OBJ
    return sum(c for c,r in terms)

def emit(path,model):
    def expr(r):
        return ' '.join(f'{"+" if q>0 else "-"} {abs(q)} x{i}' for i,q in enumerate(r,1) if q)
    with path.open('x') as f:
        f.write('Minimize\n obj: x9\nSubject To\n')
        for k,u in enumerate(model,1):
            f.write(f' r{k}: {expr(u)} >= 1\n')
        f.write('Bounds\n')
        for j in range(1,10):
            f.write(f' x{j} free\n')
        f.write('End\n')

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--emit-lp',type=Path,help='Optional deterministic model data only, no solve')
    args=p.parse_args()
    allwords=tuple(product((-1,0,1),repeat=9))
    assert all(not any(r) or dot(r,A)!=0 for r in allwords)
    ors=tuple(r for r in allwords if dot(r,A)>0)
    assert len(ors)==9841 and len(set(ors))==9841
    R=tuple(map(word,NAMES)); E=tuple(map(word,EXTRAS))
    assert set(r for r in ors if dot(r,A)==1)==set(R)|set(E)
    assert len(set(R)|set(E))==12
    primal_ok(tuple(map(F,A)),ors)
    std=tuple(zip(Y,R))
    assert dual_ok(std,ors)==161
    for j,e in enumerate(E):
        assert e==plus(R[6],R[8],times(-1,R[j]))
    print('CG9: 512 distinct 1-separated scores; 9841 oriented rows; 12 tight words verified.')
    if args.emit_lp:
        args.emit_lp.mkdir(exist_ok=True)
    vals=[]
    for j,r in enumerate(R[:7]):
        s=sum(abs(k) for k in r)
        eta=F(1,2*s)
        crossed=plus(tuple(map(F,A)),times(-(1+eta)/s,r))
        assert dot(r,crossed)==-eta and all(dot(u,crossed)>0 for u in ors if u!=r)
        at_wall=plus(tuple(map(F,A)),times(-F(1,s),r))
        assert dot(r,at_wall)==0 and all(dot(u,at_wall)>0 for u in ors if u!=r)
        model=full_model(r,ors)
        assert len(model)==9841 and set(model)-set(ors)=={times(-1,r)}
        assert set(ors)-set(model)=={r}
        cert_witness=times(2*s,crossed)
        primal_ok(cert_witness,model)
        k=7 if j<=4 else 8
        U=plus(r,R[k])
        assert U in ors and dot(U,A)==2 and U!=r
        if j==6:
            assert U==word('.....-+..')
        terms=tuple((Y[i],u) for i,u in enumerate(R) if i not in (j,k))
        terms+=((Y[k]-Y[j],times(-1,r)),(Y[k],U))
        bound=dual_ok(terms,model)
        assert bound==161+Y[k]-2*Y[j]
        print(f'R{j+1} {NAMES[j]}: U={signs(U)}, cap lower={bound}, rational adjacent witness max={cert_witness[-1]}')
        vals.append(bound)
        if args.emit_lp and j<6:
            emit(args.emit_lp/f'neighbor-R{j+1}.lp',model)
    assert vals==[207,207,205,201,193,188,168]
    for j,e in enumerate(E):
        # R_j = R7 + R9 - E_j, so substitute into the original dual.
        model=full_model(e,ors)
        terms=tuple((c,r) for i,(c,r) in enumerate(std) if i!=j)
        terms+=((Y[j],R[6]),(Y[j],R[8]),(Y[j],times(-1,e)))
        bound=dual_ok(terms,model)
        assert bound==161+2*Y[j]
        print(f'E{j+1} {EXTRAS[j]}: distinct tight flip lower={bound}')
    print('R8 and R9 negative violate sorted ordering; any other single flip leaves standard dual.')
    print('No sorted single-sign neighbor improves on 161; no numerical solve was used.')

if __name__=='__main__': main()

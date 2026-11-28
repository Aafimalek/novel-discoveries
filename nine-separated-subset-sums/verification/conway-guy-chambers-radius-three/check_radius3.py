"""Exact finite replay of the Conway–Guy nine radius-three dual substitutions."""
from collections import defaultdict
from itertools import combinations
from pathlib import Path
import sys

sys.path.insert(0,str(Path(__file__).resolve().parent/'prior-radius2'))
from check_neighbors import A,Y,NAMES,word,signs,dot,plus,times,dual_ok

R=tuple(map(word,NAMES))
R8,R9=R[7:9]
B=set(R)
U=[plus(R[j],R8) for j in range(6)]  # U6 here is R6+R8; use explicit name U6P.
U6P=U[5]; U6Q=plus(R[5],R9); U7=plus(R[6],R9)
V=[plus(U[j],R9) for j in range(6)]
W=[plus(V[j],R[5] if j<=1 else R[6] if j<=3 else R8) for j in range(5)]
assert U7==word('.....-+..') and V[5]==word('....-+...')
assert all(dot(q,A)==2 for q in U+[U6Q,U7])
assert all(dot(q,A)==3 for q in V)
assert all(dot(q,A)==4 for q in W)

def seed():
    return defaultdict(int,zip(R,Y))

def put(d,p,z):
    assert z>=0
    d[p]+=z

def change(d,p,k,z):
    # y p + z k = (z-y)(-p) + z(p+k), using z <= remaining k.
    y=d[p]
    assert 0<=y<=z<=d[k]
    d[p]=0; d[k]-=z
    put(d,times(-1,p),z-y); put(d,plus(p,k),z)

def chain(d,j,z):
    # y Rj + y R8 + z R9 = (z-y)(-Uj) + z Vj.
    y=d[R[j]]
    assert 0<=y<=d[R8] and y<=z<=d[R9]
    d[R[j]]=0; d[R8]-=y; d[R9]-=z
    put(d,times(-1,U[j]),z-y); put(d,V[j],z)

def three_link(d,j):
    # Rewrite y Rj + y R8 + y R9 = y Vj; then substitute against -Vj.
    y=d[R[j]]
    d[R[j]]=0; d[R8]-=y; d[R9]-=y
    put(d,V[j],y)
    k=R[5] if j<=1 else R[6] if j<=3 else R8
    assert plus(V[j],k)==W[j]
    change(d,V[j],k,d[k])

def proved(d,flips):
    terms=tuple((z,r) for r,z in d.items() if z)
    assert all(z>0 and set(r)<={-1,0,1} and dot(r,A)!=0 for z,r in terms)
    used={r if dot(r,A)>0 else times(-1,r) for _,r in terms}
    model={times(-1,r) if r in flips else r for r in used}
    val=dual_ok(terms,model)
    assert val>=161
    return val

def one_basis():
    # If U_j or V_j is not flipped, its earlier proof is valid unless a
    # specified used companion is flipped. An arbitrary unrelated extra
    # flip cannot affect any of these dual supports.
    out=[]
    for j in range(5):
        d=seed(); three_link(d,j)
        out.append(proved(d,{R[j],U[j],V[j]}))
    d=seed(); chain(d,5,57)
    out.append(proved(d,{R[5],U6P,U6Q}))
    assert out==[172,172,178,170,169,173]
    return out

def default_budget(js):
    # Assign the two reserves independently where possible.
    # If both R6,R7 flip, R6 consumes R8 and R7 consumes R9.
    return {j:(R8 if j<=4 or j==5 and 6 in js else R9) for j in js}

def balance(d,js,k):
    if not js:return
    assert d[k]>=sum(Y[j] for j in js)
    for j in js[:-1]:
        change(d,R[j],k,Y[j])
    change(d,R[js[-1]],k,d[k])

def exceptional(j):
    # j=R4,R5,R6 sharing a flip with R7 and U_j.
    eps=int(j!=3)
    p=plus(R[j],R[6],R9,times(eps,R8))
    assert dot(p,A)==3+eps
    d=seed()
    for q in (R[j],R[6],R8,R9): d[q]=0
    put(d,p,57)
    put(d,times(-1,U[j]),57-Y[j])
    put(d,times(-1,R[6]),32)
    put(d,R8,105-Y[j]-57*eps)
    return proved(d,{R[j],R[6],U[j]})

def two_basis_extra():
    vals=[]; details=[]
    # For each pair, only the companions of its default proof can matter.
    # U7 is the sorted difference x7-x6 and cannot be an extra flip.
    for a,b in combinations(range(7),2):
        js=(a,b); q=default_budget(js)
        words={j:plus(R[j],q[j]) for j in js}
        for j in js:
            if j==6:continue
            extra=words[j]; other=b if j==a else a
            assert dot(extra,A)==2
            d=seed()
            if j<=4:
                if other==6 and j>=3:
                    val=exceptional(j)
                    details.append((j+1,other+1,signs(extra),val)); vals.append(val)
                    continue
                chain(d,j,32 if other==6 else 57)
                # A lower row or R6 can share remaining R8. R7 uses R9.
                k=R9 if other==6 else R8
                change(d,R[other],k,d[k])
            elif other<=4:
                # The default companion was U6Q; use R8 for both instead.
                assert extra==U6Q
                balance(d,(other,5),R8)
            else:
                assert (j,other)==(5,6) and extra==U6P
                val=exceptional(5)
                details.append((6,7,signs(extra),val)); vals.append(val)
                continue
            val=proved(d,{R[a],R[b],extra})
            details.append((a+1,b+1,signs(extra),val)); vals.append(val)
    assert len(vals)==36 and min(vals)==162
    return details

def three_basis():
    out=[]
    for js in combinations(range(7),3):
        d=seed(); k=default_budget(js)
        for source in (R8,R9):
            balance(d,tuple(j for j in js if k[j]==source),source)
        out.append(proved(d,{R[j] for j in js}))
    assert len(out)==35 and min(out)==170
    return out

if __name__=='__main__':
    o=one_basis(); m=two_basis_extra(); t=three_basis()
    assert [exceptional(j) for j in (3,4,5)]==[270,201,180]
    print('One basis and both active extra flips:',len(o),'proved bounds',o)
    print('Two basis and one harmful companion flip:',len(m),'minimum proved bound',min(p[-1] for p in m))
    print('Three exceptional integer duals:',[(j+1,7,exceptional(j)) for j in (3,4,5)])
    print('Three basis flips:',len(t),'minimum proved bound',min(t))
    print('Remaining sign sets reduce to original or radius-two certificates; no solver used.')

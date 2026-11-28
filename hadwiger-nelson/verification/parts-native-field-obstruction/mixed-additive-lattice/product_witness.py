#!/usr/bin/env python3
"""Check the fixture's exact Cartesian structure and direct colorings, no solver."""
import argparse,json
from itertools import combinations,product
from pathlib import Path
from fixture import CW,Z,TWO,add,mul,scale,sub,edge_form,DEN

def lat(a,b):
    assert (a-b)%2==0
    return ((a-b)//2,b)

def read(out):
    g=json.loads((out/'exact-graph.json').read_bytes())
    assert g['scale']==DEN==24 and g['generator_squares']==[33,-3,-7]
    P=[tuple(q) for q in g['vertices']]
    E={tuple(e) for e in g['unit_edges']}
    assert len(P)==len(set(P))==931 and len(E)==len(g['unit_edges'])==5250
    return P,E,g['terminals']

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('out',type=Path)
    p.add_argument('witness',type=Path)
    args=p.parse_args()
    P,E,(x,z)=read(args.out)
    W={lat(a,b):(a,0,b,0,0,0,0,0) for a,b in CW}
    T={(m+u,n+v):scale(add(a,b),12) for (m,n),a in W.items() for (u,v),b in W.items()}
    A={v:scale(mul((0,1,1,0,0,0,0,0),w),2) for v,w in W.items()}
    B={v:scale(mul((3,0,0,0,1,0,0,0),w),3) for v,w in W.items()}
    assert len(T)==19 and len(W)==7
    coords={add(add(T[t],A[a]),B[b]):(t,a,b) for t,a,b in product(T,W,W)}
    assert len(coords)==len(P)==19*7*7 and set(coords)==set(P)
    assert P[x]==Z and P[z]==TWO
    pos={coords[q]:i for i,q in enumerate(P)}
    def unit_edges(U):
        return {(u,v) for u,v in combinations(U,2)
                if (u[0]-v[0])**2+(u[0]-v[0])*(u[1]-v[1])+(u[1]-v[1])**2==1}
    et,ew=unit_edges(T),unit_edges(W)
    assert len(et)==42 and len(ew)==12
    S=set()
    def ins(u,v):S.add(tuple(sorted((pos[u],pos[v]))))
    for uv,a,b in product(et,W,W):ins((uv[0],a,b),(uv[1],a,b))
    for t,uv,b in product(T,ew,W):ins((t,uv[0],b),(t,uv[1],b))
    for t,a,uv in product(T,W,ew):ins((t,a,uv[0]),(t,a,uv[1]))
    assert E==S
    # Direct re-evaluation of the entire Euclidean unit-distance graph,
    # not merely union of the Cartesian edges from the previous proof.
    assert E=={(i,j) for i,j in combinations(range(len(P)),2)
               if edge_form(sub(P[i],P[j]))==(DEN**2,0,0,0)}
    C=[]; R=[]
    for q in P:
        mn=coords[q]
        m=sum(a for a,b in mn);n=sum(b for a,b in mn)
        C.append((m+2*n)%3)
        R.append((m%2)+2*(n%2))
    Aeq=C.copy(); Aeq[x]=Aeq[z]=3
    assert all(C[i]!=C[j] and Aeq[i]!=Aeq[j] and R[i]!=R[j] for i,j in E)
    assert Aeq[x]==Aeq[z] and R[x]==R[z]
    tri=sorted(pos[((m,n),(0,0),(0,0))] for m,n in ((0,0),(1,0),(0,1)))
    assert all(e in E for e in combinations(tri,2))
    result={'triangle_ids':tri,'terminals':[x,z],'proper_three':C,
            'recolored_equal_four':Aeq,'parity_equal_four':R}
    args.witness.write_text(json.dumps(result,separators=(',',':'))+'\n')
    print('Checked χ=3 (explicit 3-coloring and triangle) and two exact 4-colorings with equal terminals.')

if __name__=='__main__':main()

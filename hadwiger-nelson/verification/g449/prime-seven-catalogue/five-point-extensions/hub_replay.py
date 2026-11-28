#!/usr/bin/env python3
"""Exact grid five-point extension checker for a base-degree-one hub."""
from argparse import ArgumentParser
from collections import Counter
from itertools import combinations, product
from pathlib import Path
from two_point_replay import absent, checked_colourings, grid_neighbours, load_data


def encoded(v):
    return sum(a << (8*i) for i,a in enumerate(v))


def list_colourable(masks, adjacency):
    # Explicit exact list-coloring on five vertices. As soon as a color is
    # chosen, filter it from unassigned neighbors. Use minimum domain first.
    def dfs(ls, unassigned):
        if not unassigned:
            return True
        i = min(unassigned,key=lambda j:ls[j].bit_count())
        remain = tuple(j for j in unassigned if j!=i)
        choice = ls[i]
        while choice:
            b = choice & -choice
            nxt = tuple((a & ~b) if (adjacency[i]>>j&1) else a
                        for j,a in enumerate(ls))
            if dfs(nxt,remain):
                return True
            choice -= b
        return False
    return dfs(masks,tuple(range(5)))


def brute(masks, adjacency):
    edge = [(i,j) for i in range(5) for j in range(i+1,5) if adjacency[i]>>j&1]
    allowed = [tuple(c for c in range(5) if m>>c&1) for m in masks]
    return any(all(c[i]!=c[j] for i,j in edge) for c in product(*allowed))


def verify_hub_cases(pts, dirs, banks, cross_check):
    centers,old=grid_neighbours(pts,dirs)
    def decomp(a):
        return tuple(x-128 for x in a)
    hubs={encoded(decomp(x)):i for x,i in centers.items() if x not in old and isinstance(i,int)}
    rims=sorted((decomp(x),v) for x,v in centers.items() if x not in old and isinstance(v,list))
    assert len(hubs)==222264 and len(rims)==7056
    del centers,old
    R=[encoded(x) for x,_ in rims]
    N=[len(v) for _,v in rims]
    L=[tuple(absent(v,c) for c in banks) for _,v in rims]
    D={encoded(d) for d in dirs}
    B=max(abs(a) for q in pts for a in q)
    S=max(abs(a) for q in dirs for a in q)
    H=max(abs(a) for q,_ in rims for a in q)
    # In each encoded lookup, digitwise subtraction from the sought
    # direction or hub yields coefficients <128 in absolute value.
    assert max(H+B+2*S,2*H+S)<128
    assert len(D)==len(dirs)
    nbs={}
    for j,x in enumerate(R):
        for d in D:
            q=x+d
            if q in hubs:
                nbs.setdefault(q,[]).append(j)
    incid=sum(map(len,nbs.values()))
    assert incid==109683
    print("Hub/rim available incidence pairs:",incid,flush=True)
    residual=[]
    support=[0]*len(banks)
    raw=tested=0
    shapes=Counter()
    for h,ns in sorted(nbs.items()):
        if len(ns)<4:
            continue
        assert all(i<j for i,j in zip(ns,ns[1:]))
        links=[{k for k in ns if R[j]-R[k] in D} for j in ns]
        assert all(len(s)<=2 and j not in s for j,s in zip(ns,links))
        nb=dict(zip(ns,links))
        base=hubs[h]
        hub_masks=tuple(31^(1<<c[base]) for c in banks)
        for quad in combinations(ns,4):
            raw+=1
            W=set(quad)
            ds=[len(nb[j]&W) for j in quad]
            if any(N[i]+d<4 for i,d in zip(quad,ds)):
                continue
            tested+=1
            shape=sum(ds)//2
            assert shape<=3
            shapes[shape]+=1
            ad=[0b11110]+[1+sum(1<<k for k,b in enumerate(quad,1) if b in nb[j]) for j in quad]
            A,B,C,E=[L[j] for j in quad]
            for s,M in enumerate(zip(hub_masks,A,B,C,E)):
                ok=all(M) and list_colourable(M,ad)
                if cross_check:
                    assert ok==brute(M,ad)
                if ok:
                    support[s]+=1
                    break
            else:
                residual.append((h,quad))
    assert raw==872165 and tested==6839
    assert shapes=={0:1813,1:4235,2:791}
    print("Four-rim sets:",raw,"minimum-degree eligible:",tested,flush=True)
    print("Eligible shapes by rim edge count:",dict(sorted(shapes.items())),flush=True)
    print("Bank first success distribution:",support,flush=True)
    assert not residual,residual[:5]
    print("No residual configurations.",flush=True)
    if cross_check:
        print("Independent direct Cartesian product list test agreed on every inspected vector.",flush=True)


def main():
    pa=ArgumentParser(description=__doc__)
    pa.add_argument('input',type=Path)
    pa.add_argument('catalogue',type=Path)
    pa.add_argument('single_witnesses',type=Path)
    pa.add_argument('--cross-check',action='store_true')
    a=pa.parse_args()
    pts, orig, edges, dirs=load_data(a.input,a.catalogue)
    banks,_=checked_colourings(orig,edges,a.single_witnesses)
    verify_hub_cases(pts,dirs,banks[:18],a.cross_check)



if __name__=="__main__":
    main()

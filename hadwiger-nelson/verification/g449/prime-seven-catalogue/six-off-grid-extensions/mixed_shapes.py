#!/usr/bin/env python3
"""Small finite shape classification for six added points, conditional on five theorem."""
from itertools import combinations, permutations

V=range(6)
E=list(combinations(V,2))
ID={e:i for i,e in enumerate(E)}


def basic(mask):
    nb=[set() for _ in V]
    for k,(u,v) in enumerate(E):
        if mask>>k&1:
            nb[u].add(v)
            nb[v].add(u)
    if any(len(nb[u]&nb[v])>2 for u,v in E):
        return None
    for s in nb:
        # Unit edges between neighbors of a point follow angles ±60°. With ≤5
        # neighbors, their locus must be degree≤2 and each nonempty comp a path.
        rest=set(s)
        while rest:
            root=rest.pop()
            front=[root]
            deg=0
            count=0
            while front:
                u=front.pop()
                t=nb[u]&s
                if len(t)>2:return None
                deg+=len(t)
                count+=1
                nxt=t&rest
                front.extend(nxt)
                rest-=nxt
            if deg!=2*(count-1):return None
    return nb


def allowed(nb,r):
    off=set(range(r))
    grid=set(range(r,6))
    deg=list(map(len,nb))
    if any(deg[x]<3 for x in off):
        return False
    for x in off:
        g=nb[x]&grid
        if any(y in nb[z] for y,z in combinations(g,2)):return False
        d=deg[x]
        if d==3 and any(deg[y]<=2 for y in g):return False
        # Grid base degree lower bound is max(0,5-deg[y]).
        high=sum(deg[y]<=1 for y in g)
        if high>=3 or (d==4 and high>=2):return False
    return True


def translate_and_apex(nb,r):
    off=set(range(r))
    grid=set(range(r,6))
    ts=[set(tr) for tr in combinations(V,3)
        if all(v in nb[u] for u,v in combinations(tr,2))]
    if all(len(ns)==3 for ns in nb):
        for A in ts:
            B=set(V)-A
            if B not in ts:continue
            # A unit triangular prism is a translation (see README).
            if (A<=grid and 0<len(B&grid)<3) or (B<=grid and 0<len(A&grid)<3):
                return False
    for A in ts:
        if not A<=off:continue
        ext=[g for g in grid if len(nb[g]&A)==2]
        # Distinct exterior apices of the same equilateral triangle have
        # distance two and their unique common unit neighbor is in A.
        for u,v in combinations(ext,2):
            if v in nb[u] or (nb[u]&nb[v])-A: return False
    return True


def prism_list_colorable(nb,r):
    off=set(range(r))
    grid=set(range(r,6))
    if not all(len(ns)==3 for ns in nb):return False
    has_partition=any(all(v in nb[u] for u,v in combinations(block,2))
                      and all(v in nb[u] for u,v in combinations(set(V)-block,2))
                      for tr in combinations(V,3) for block in [set(tr)])
    return has_partition and all(nb[g]&off for g in grid)


def expansion(mask, perms):
    active=[e for k,e in enumerate(E) if mask>>k&1]
    return {sum(1<<ID[tuple(sorted((p[u],p[v])))] for u,v in active) for p in perms}


def main():
    B=[(m,g) for m in range(1<<15) if (g:=basic(m)) is not None]
    for r in range(1,7):
        coarse=[m for m,g in B if allowed(g,r)]
        geom=[m for m,g in B if allowed(g,r) and translate_and_apex(g,r)]
        cams=[m for m,g in B if allowed(g,r) and translate_and_apex(g,r)
              and not prism_list_colorable(g,r)]
        # Every remaining pattern has the geometric target of the exact scans.
        for m in cams:
            nb=basic(m)
            if r==2:
                shared={v for v in (nb[0]&nb[1]) if v>=2 and len(nb[v])<=3}
                assert 1 in nb[0] and len(shared)==2
            if r==3:
                off={0,1,2}; grid={3,4,5}
                assert all(nb[u]&off==off-{u} and len(nb[u]&grid)==2 for u in off)
                assert {frozenset(nb[v]) for v in grid}=={frozenset(c) for c in combinations(off,2)}
        perms=[p+q for p in permutations(range(r)) for q in permutations(range(r,6))]
        visited=set()
        shapes=[]
        for m in cams:
            if m not in visited:
                shapes.append([e for k,e in enumerate(E) if m>>k&1])
                visited |= expansion(m,perms)
        assert set(cams)==visited
        expect={1:(0,0,0,0),2:(72,48,48,4),3:(30,12,6,1),4:(36,36,0,0),5:(60,60,0,0),6:(60,60,0,0)}
        # The residual geometry needed by the separate exact pair and
        # exterior-apex scans, verified for every surviving labeled graph.
        for m in cams:
            nb=basic(m)
            if r==2:
                assert 1 in nb[0] and len(nb[0]&nb[1])==2
                assert all(len(nb[v])<=3 for v in nb[0]&nb[1])
            elif r==3:
                assert all(v in nb[u] for u,v in combinations(range(3),2))
                assert all(len(nb[u])==4 for u in range(3))
                assert all(len(nb[u])==2 and nb[u]<=set(range(3)) for u in range(3,6))
                assert len({frozenset(nb[u]) for u in range(3,6)})==3
        assert (len(coarse),len(geom),len(cams),len(shapes))==expect[r]
        print(r,"off:",len(coarse),"coarse states;",len(geom),"after geometry;",
              len(cams),"after prism lists;",len(shapes),"shapes",shapes)


if __name__=="__main__":
    main()

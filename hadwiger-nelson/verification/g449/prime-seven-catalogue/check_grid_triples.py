#!/usr/bin/env python3
"""Prove five-colorability for three added denominator-seven grid points."""
import argparse,json
from collections import Counter,defaultdict
from itertools import combinations
from pathlib import Path

from check_extensions import solve
from two_point_replay import load_data, checked_colourings


def add(x,y):
    return tuple(a+b for a,b in zip(x,y))


def masks(ns,colors):
    ans=[]
    for C in colors:
        used=0
        for i in ns:
            used|=1<<C[i]
        ans.append(31^used)
    return tuple(ans)


def vertex_flags(row):
    ok=0
    only=[0]*5
    allowed=[0]*5
    for i,a in enumerate(row):
        if a:
            ok|=1<<i
        if a.bit_count()==1:
            only[a.bit_length()-1]|=1<<i
        for c in range(5):
            if a>>c&1:
                allowed[c]|=1<<i
    return ok,only,allowed


def pair_ok(a,b):
    x,s,_=a
    y,t,_=b
    z=0
    for i,j in zip(s,t):
        z|=i&j
    return x&y&~z


def path_ok(a,b,c):
    x,s,_=a
    _,_,A=b
    z,t,_=c
    return x&z&sum_disjunction(B&~e&~f for B,e,f in zip(A,s,t))


def sum_disjunction(xs):
    acc=0
    for x in xs:
        acc|=x
    return acc


def triangle(a,b,c):
    for x,y,z in zip(a,b,c):
        if x and y and z and (x|y).bit_count()>=2 and (x|z).bit_count()>=2 and (y|z).bit_count()>=2 and (x|y|z).bit_count()>=3:
            return True
    return False


def main():
    p=argparse.ArgumentParser()
    p.add_argument("input",type=Path)
    p.add_argument("catalogue",type=Path)
    p.add_argument("witnesses",type=Path)
    p.add_argument("--residual",type=Path)
    p.add_argument("--solver", help="find a five-color witness for the residual triples")
    args=p.parse_args()
    points,base,edges,steps=load_data(args.input,args.catalogue)
    cs,_=checked_colourings(base,edges,args.witnesses)
    old=set(points)
    outside=defaultdict(set)
    for i,x in enumerate(points):
        for step in steps:
            y=add(x,step)
            if y not in old:
                outside[y].add(i)
    assert len(outside)==229320
    high=sorted(x for x,ns in outside.items() if len(ns)>=3)
    high5=[i for i,x in enumerate(high) if len(outside[x])>=5]
    assert (len(high),len(high5))==(2429,574)
    idx={x:i for i,x in enumerate(high)}
    nb=[{idx[y] for step in steps if (y:=add(x,step)) in idx} for x in high]
    assert all(i not in v and all(i in nb[j] for j in v) for i,v in enumerate(nb))
    rows=[masks(outside[x],cs) for x in high]
    flags=[vertex_flags(v) for v in rows]
    av=[f[0] for f in flags]
    exception=[i for i in high5 if not (av[i]&1)]
    assert len(exception)==34
    unresolved=[]
    def fail(shape,i,j,k):
        unresolved.append((shape,i,j,k))

    # No-edge triples. Vertices with <=4 base neighbors never have an
    # empty list; reduce those to a previous two-point result.
    types=defaultdict(list)
    for i in high5:
        types[av[i]].append(i)
    for i in exception:
        for ax,ay in combinations(sorted(types),2):
            if av[i]&ax&ay: continue
            for j in types[ax]:
                for k in types[ay]:
                    if len({i,j,k})==3 and j not in nb[i] and k not in nb[i] and k not in nb[j]:
                        fail(0,i,j,k)
        # Equal masks similarly; both third-party vertices must exist.
        for ax,ids in types.items():
            if av[i]&ax: continue
            for j,k in combinations(ids,2):
                if len({i,j,k})==3 and j not in nb[i] and k not in nb[i] and k not in nb[j]:
                    fail(0,i,j,k)
    # A one-edge triple can reduce to a two-point result if the isolated
    # vertex has at most four base neighbors. Check higher-degree thirds.
    eh=0
    for i,ns in enumerate(nb):
        for j in ns:
            if j<=i: continue
            eh+=1
            good=pair_ok(flags[i],flags[j])
            assert good  # Independently check this edge across our color bank.
            for ax,vs in types.items():
                if good&ax: continue
                for k in vs:
                    if k!=i and k!=j and k not in nb[i] and k not in nb[j]:
                        fail(1,i,j,k)
    pathct=0
    tric=0
    for j,ns in enumerate(nb):
        for i,k in combinations(sorted(ns),2):
            if k in nb[i]:
                if i<j<k:
                    tric+=1
                    if not triangle(rows[i],rows[j],rows[k]):
                        fail(3,i,j,k)
            else:
                pathct+=1
                if not path_ok(flags[i],flags[j],flags[k]):
                    fail(2,i,j,k)
    print("outside grid points with >=3 / >=5 base neighbors:",len(high),len(high5))
    print("nonempty-mask types among high-five points:",len(types))
    print("high-candidate edges / induced paths / triangles:",eh,pathct,tric)
    print("not covered by the original 35-coloring bank, by shape:",dict(sorted(Counter(x[0] for x in unresolved).items())))
    triples=sorted({tuple(sorted((i,j,k))) for _,i,j,k in unresolved})
    print("distinct residual triples:",len(triples),flush=True)
    if not triples:
        return
    assert args.residual is not None
    ids=sorted({i for tr in triples for i in tr})
    local={i:j+449 for j,i in enumerate(ids)}
    more=len(ids)
    full=set(edges)
    full|={(i,local[j]) for j in ids for i in outside[high[j]]}
    full|={(local[i],local[j]) for i in ids for j in nb[i] if i<j and j in local}
    print("union of residual points:",more,"new vertices;",len(full),"total edges",flush=True)
    payload={"points":[list(high[i]) for i in ids],
             "triples":[list(local[i]-449 for i in tr) for tr in triples],
             "edges":len(full)}
    if args.solver:
        status,y=solve(args.solver,6.0,449+more,full,[])
        print("combined residual search:",status,flush=True)
        assert status=="sat-witness-checked"
        payload["colors"]=y
        args.residual.write_text(json.dumps(payload,indent=2)+"\n")
    saved=json.loads(args.residual.read_text())
    assert all(saved[k]==v for k,v in payload.items())
    y=saved["colors"]
    assert len(y)==449+more and set(y)==set("01234")
    assert all(y[i]!=y[j] for i,j in full)
    print("verified one five-color witness covering all residual triples",flush=True)


if __name__=="__main__":
    main()

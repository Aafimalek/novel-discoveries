#!/usr/bin/env python3
"""Export every eligible grid vertex and recompute every induced unit edge."""
import argparse, json
from pathlib import Path
from two_point_replay import load_data, checked_colourings, grid_neighbours
from check_grid_triples import masks


def main():
    arg = argparse.ArgumentParser()
    arg.add_argument("base", type=Path)
    arg.add_argument("catalogue", type=Path)
    arg.add_argument("single", type=Path)
    arg.add_argument("triple", type=Path)
    arg.add_argument("target", type=Path)
    a=arg.parse_args()
    pts,base,edges,dirs = load_data(a.base,a.catalogue)
    colorings,_ = checked_colourings(base,edges,a.single)
    grid,old = grid_neighbours(pts,dirs)
    pxy=sorted(x for x,v in grid.items() if isinstance(v,list) and x not in old)
    assert len(pxy)==7056
    ids={p:i for i,p in enumerate(pxy)}
    ns=[grid[p] for p in pxy]
    # Bytes here only encode exact coefficients; no modular operations.
    coords=[tuple(u-128 for u in p) for p in pxy]
    assert all(-128 <= u+d < 128 for u in [min(min(x) for x in coords),max(max(x) for x in coords)] for d in [min(min(x) for x in dirs),max(max(x) for x in dirs)])
    graph=[set() for _ in ids]
    for i,x in enumerate(pxy):
        for d in dirs:
            y=bytes(u+v for u,v in zip(x,d))
            j=ids.get(y,-1)
            if j>=0:
                graph[i].add(j)
    assert all(i not in v and all(i in graph[j] for j in v) for i,v in enumerate(graph))
    # Verify the additional 36th color vector on the full induced residual union.
    tr=json.loads(a.triple.read_text())
    trpoints=[tuple(v) for v in tr["points"]]
    trids=[ids[bytes(u+128 for u in v)] for v in trpoints]
    assert len(trids)==len(set(trids))==54
    c=tuple(map(int,tr["colors"]))
    assert len(c)==449+54 and set(c)==set(range(5))
    tr_edges={(i,449+j) for j,k in enumerate(trids) for i in ns[k]}
    tr_edges.update((449+i,449+j) for i,k in enumerate(trids)
                    for j,l in enumerate(trids) if i<j and l in graph[k])
    assert len(tr_edges)+len(edges)==tr["edges"]==2545
    assert all(c[i]!=c[j] for i,j in edges|tr_edges)
    colorings.append(c[:449])
    assert len(colorings)==36
    raw={"coordinates":coords,"base_neighbors":ns,"base_edges":sorted(edges),
         "added_edges":[(i,j) for i,v in enumerate(graph) for j in sorted(v) if i<j],
         "base_colorings":colorings}
    a.target.mkdir(parents=True,exist_ok=True)
    (a.target/"data.json").write_text(json.dumps(raw,separators=(",",":"))+"\n")
    with (a.target/"data.txt").open("w") as f:
        print(len(ids),len(colorings),len(raw["added_edges"]),file=f)
        for n in ns:
            print(len(n),*masks(n,colorings),file=f)
        for i,j in raw["added_edges"]:
            print(i,j,file=f)
    print("candidate degree >=2 / >=3 / >=4 / >=5:",len(ns),*(sum(len(x)>=d for x in ns) for d in range(3,6)))
    print("candidate edges:",len(raw["added_edges"]),"maximum internal degree:",max(map(len,graph)))
    print("36 bank colorings and induced triple residual witness verified")


if __name__=="__main__": main()

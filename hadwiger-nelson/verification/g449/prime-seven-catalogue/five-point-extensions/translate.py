#!/usr/bin/env python3
"""Recompute candidate list masks for the original 36 and verified optional banks."""
import json,sys
from pathlib import Path
base,out,*extras = map(Path,sys.argv[1:])
data=json.loads(base.read_text())
point_ids={tuple(v):i for i,v in enumerate(data["coordinates"])}
edges=set(map(tuple,data["added_edges"]))
colors=data["base_colorings"]
for f in extras:
    w=json.loads(f.read_text())
    c=tuple(map(int,w["colors"]))
    p=[point_ids[tuple(v)] for v in w["points"]]
    assert len(p)==len(set(p)) and len(c)==449+len(p)==w["vertices"]
    assert all(0<=v<5 for v in c)
    eval_edges=set(map(tuple,data["base_edges"]))
    eval_edges.update((u,449+j) for j,i in enumerate(p) for u in data["base_neighbors"][i])
    rev={i:j+449 for j,i in enumerate(p)}
    eval_edges.update((rev[i],rev[j]) for i,j in edges if i in rev and j in rev)
    assert w["edges"]==len(eval_edges) and all(c[i]!=c[j] for i,j in eval_edges)
    colors.append(c[:449])
assert 36<=len(colors)<64
assert all(len(c)==449 and all(c[i]!=c[j] for i,j in data["base_edges"]) for c in colors)
with out.open("w") as f:
    print(len(point_ids),len(colors),len(edges),file=f)
    for ns in data["base_neighbors"]:
        ls=[31^sum(1<<j for j in {c[i] for i in ns}) for c in colors]
        print(len(ns),*ls,file=f)
    for i,j in sorted(edges):print(i,j,file=f)

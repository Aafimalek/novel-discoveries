#!/usr/bin/env python3
"""Verify the induced union of the residual quartets, using a stored or searched witness."""
import argparse
import hashlib
import json
import subprocess
from collections import Counter
from itertools import combinations
from pathlib import Path
from check_extensions import instance


def main():
    p=argparse.ArgumentParser()
    p.add_argument("data",type=Path)
    p.add_argument("residual",type=Path)
    p.add_argument("witness",type=Path)
    p.add_argument("--solver")
    p.add_argument("--seconds",type=float,default=30)
    p.add_argument("--cnf",type=Path)
    args=p.parse_args()
    data=json.loads(args.data.read_text())
    rows=[tuple(map(int,line.split())) for line in args.residual.read_text().splitlines()]
    base_edges=set(map(tuple,data["base_edges"]))
    graph=set(map(tuple,data["added_edges"]))
    R=[r[1:] for r in rows]
    assert len(set(R))==len(R) and all(len(r)==4 and list(sorted(set(r)))==list(r) for r in R)
    def edge(a,b):return tuple(sorted((a,b))) in graph
    for shape,*S in rows:
        h={v for v in S}
        sizes=[]
        while h:
            z={h.pop()}
            while (nexts:={i for i in h if any(edge(i,j) for j in z)}):
                h-=nexts
                z|=nexts
            sizes.append(len(z))
        assert sorted(sizes)==[[1,1,1,1],[1,1,2],[2,2],[1,3],[4]][shape]
        assert all(len(data["base_neighbors"][i])+sum(edge(i,j) for j in S)>=5 for i in S)
    V=sorted(set(v for row in R for v in row))
    name={v:449+j for j,v in enumerate(V)}
    add={(u,name[v]) for v in V for u in data["base_neighbors"][v]}
    add|={(name[i],name[j]) for i,j in graph if i in name and j in name}
    full=base_edges|add
    fixed=next({(i,0),(j,1),(k,2)} for i,j in sorted(base_edges) for k in range(j+1,449)
               if (i,k) in base_edges and (j,k) in base_edges)
    payload={"points":[data["coordinates"][i] for i in V],
             "vertices":len(V)+449,"edges":len(full),
             "residual_counts":{str(k):v for k,v in sorted(Counter(row[0] for row in rows).items())},
             "enumeration_sha256":hashlib.sha256(args.residual.read_bytes()).hexdigest()}
    print(payload["vertices"],"vertices;",payload["edges"],"edges;",
          len(rows),"distinct residual quartets",flush=True)
    if args.solver:
        formula=instance(payload["vertices"],full,fixed)
        if args.cnf:args.cnf.write_text(formula)
        r=subprocess.run([args.solver],input=formula,text=True,capture_output=True,
                         timeout=args.seconds)
        if r.returncode!=10:
            raise SystemExit(f"no SAT witness, rc={r.returncode}")
        yes={int(l) for line in r.stdout.splitlines() if line.startswith("v ")
             for l in line[2:].split() if int(l)>0}
        sets=[[c for c in range(5) if 1+5*i+c in yes] for i in range(payload["vertices"])]
        assert all(len(s)==1 for s in sets)
        colors="".join(str(s[0]) for s in sets)
    else:
        witness=json.loads(args.witness.read_text())
        assert all(witness[k]==payload[k] for k in payload)
        colors=witness["colors"]
    assert len(colors)==payload["vertices"] and set(colors)==set("01234")
    assert all(colors[i]!=colors[j] for i,j in full)
    assert all(int(colors[i])==c for i,c in fixed)
    print("Verified all induced edges of the common five-color witness",flush=True)
    if args.solver:
        payload["colors"]=colors
        args.witness.write_text(json.dumps(payload,indent=2)+"\n")


if __name__=="__main__": main()

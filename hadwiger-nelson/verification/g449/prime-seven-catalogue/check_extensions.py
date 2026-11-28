#!/usr/bin/env python3
"""One-vertex extension checks for the G449 five-coloring. Exact integer geometry."""
import argparse
from collections import defaultdict
from hashlib import sha256
import json
from pathlib import Path
import subprocess
from audit_layers import PINNED, parse_sparse6, sub


def input_data(source, catalogue_path):
    raw = {name: (source / name).read_bytes() for name in PINNED}
    assert {key: sha256(val).hexdigest() for key, val in raw.items()} == PINNED
    records = [tuple(map(int, line.split()))
               for line in raw["G449.k21"].decode().splitlines()[1:] if line]
    assert all(len(r) == 13 and all(a % 7 == 0 for a in r[:-1]) for r in records)
    points = [tuple(a // 7 for a in r[:-1]) for r in records]
    original = [r[-1] for r in records]
    n, edges = parse_sparse6(raw["G449.s6"])
    assert n == len(points) == len(set(points)) == 449
    assert len(edges) == 2198 and all(original[x] != original[y] for x,y in edges)
    rows = [tuple(map(int, line.split()))
            for line in catalogue_path.read_text().splitlines()[1:] if line]
    assert len(rows) == 273 and all(r[1] in (1,7) for r in rows)
    steps = {tuple(sign*a*(7//r[1]) for a in r[2:]) for r in rows for sign in (-1,1)}
    assert len(steps) == 546
    return points, original, edges, steps


def candidates(points, colors, steps):
    old = set(points)
    outside = defaultdict(set)
    for i, x in enumerate(points):
        for d in steps:
            y = tuple(a+b for a,b in zip(x,d))
            if y not in old:
                outside[y].add(i)
    blocked = sorted((x, sorted(ids)) for x, ids in outside.items()
                     if len({colors[i] for i in ids}) == 5)
    return len(outside), blocked


def instance(n, edges, fix):
    def var(x, c): return 5*x+c+1
    clauses = [[var(x,c) for c in range(5)] for x in range(n)]
    clauses += [[-var(x,c),-var(x,d)] for x in range(n) for c in range(5) for d in range(c)]
    clauses += [[-var(x,c),-var(y,c)] for x,y in sorted(edges) for c in range(5)]
    clauses += [[var(i,c)] for i,c in fix]
    return f"p cnf {5*n} {len(clauses)}\n" + "".join(" ".join(map(str, row))+" 0\n" for row in clauses)


def solve(solver, seconds, n, edges, fix):
    try:
        r = subprocess.run([solver,"-q"], input=instance(n,edges,fix),
                           text=True,capture_output=True,timeout=seconds)
    except subprocess.TimeoutExpired:
        return "timeout", None
    if r.returncode==20:
        return "unsat-unverified", None
    assert r.returncode==10, (r.returncode,r.stderr,r.stdout)
    positive = {int(a) for line in r.stdout.splitlines() if line.startswith("v ")
                for a in line[2:].split() if int(a)>0}
    rows = [[c for c in range(5) if 5*i+c+1 in positive] for i in range(n)]
    assert all(len(r)==1 for r in rows)
    colors = [r[0] for r in rows]
    assert all(colors[i] != colors[j] for i,j in edges)
    assert all(colors[i] == c for i,c in fix)
    return "sat-witness-checked", "".join(map(str,colors))


def combined_graph(edges, cand, steps):
    new=set(edges)
    new|={(i,449+k) for k,(_,ns) in enumerate(cand) for i in ns}
    new|={(449+i,449+j) for i,(x,_) in enumerate(cand) for j,(y,_) in enumerate(cand)
          if i<j and sub(x,y) in steps}
    return new


def verify(path, edges, cand, steps, triangle):
    report=json.loads(path.read_text())
    assert tuple(report["triangle"])==triangle and len(report["single"])==len(cand)
    for i,((x,ns),row) in enumerate(zip(cand,report["single"])):
        assert tuple(row["point"])==x and row["neighbors"]==ns
        assert row["status"]=="sat-witness-checked"
        check_colors(row["colors"],450,edges|{(v,449) for v in ns},triangle)
    combined=report["combined"]
    new=combined_graph(edges,cand,steps)
    assert combined is not None and combined["edges"]==len(new)
    assert combined["status"]=="sat-witness-checked"
    check_colors(combined["colors"],449+len(cand),new,triangle)
    print(f"Verified {len(cand)} single-extension five-colorings.")
    print(f"Verified one five-coloring for all {449+len(cand)} vertices and {len(new)} edges.")


def check_colors(colors, n, edges, triangle):
    assert len(colors)==n and set(colors)==set("01234")
    assert all(colors[i]!=colors[j] for i,j in edges)
    assert "".join(colors[i] for i in triangle)=="012"


def main():
    p=argparse.ArgumentParser()
    p.add_argument("input",type=Path)
    p.add_argument("catalogue",type=Path)
    p.add_argument("solver")
    p.add_argument("output",type=Path)
    p.add_argument("--seconds",type=float,default=0.8)
    p.add_argument("--skip-combined",action="store_true")
    p.add_argument("--verify-only",action="store_true",help="verify JSON without running the solver")
    a=p.parse_args()
    points, colors, edges, steps=input_data(a.input,a.catalogue)
    total,cand=candidates(points,colors,steps)
    assert total==229320 and len(cand)==34
    print(f"{total} distinct outside neighbors; {len(cand)} block the supplied five-coloring.")
    # Fix the colors of a triangle only, a harmless renaming of any coloring.
    neigh=[{j for i,j in edges if i==v}|{i for i,j in edges if j==v} for v in range(449)]
    triangle=next((i,j,k) for i,j in sorted(edges) for k in sorted(neigh[i]&neigh[j]))
    fix=list(zip(triangle,range(3)))
    if a.verify_only:
        verify(a.output,edges,cand,steps,triangle)
        return
    answers=[]
    for x, ns in cand:
        new=edges|{(i,449) for i in ns}
        st,w=solve(a.solver,a.seconds,450,new,fix)
        answers.append({"point":x,"neighbors":ns,"status":st,"colors":w})
        print(len(answers),st,flush=True)
    combined=None
    if not a.skip_combined:
        new=combined_graph(edges,cand,steps)
        st,w=solve(a.solver,4*a.seconds,449+len(cand),new,fix)
        combined={"edges":len(new),"status":st,"colors":w}
        print("combined",len(new),st,flush=True)
    a.output.write_text(json.dumps({"triangle":triangle,"single":answers,"combined":combined},indent=2)+"\n")


if __name__=="__main__":
    main()

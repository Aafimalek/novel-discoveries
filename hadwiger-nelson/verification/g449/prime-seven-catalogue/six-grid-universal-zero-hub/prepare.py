#!/usr/bin/env python3
"""Emit pinned exact G449 coordinates, all grid directions, and verified palettes."""
from argparse import ArgumentParser
from pathlib import Path
import json
from two_point_replay import checked_colourings,load_data


def main():
    p=ArgumentParser(description=__doc__)
    p.add_argument("input",type=Path)
    p.add_argument("catalogue",type=Path)
    p.add_argument("single",type=Path)
    p.add_argument("output",type=Path)
    p.add_argument("extra",type=Path,nargs="*")
    a=p.parse_args()
    Q,orig,E,D=load_data(a.input,a.catalogue)
    banks,_=checked_colourings(orig,E,a.single)
    for f in a.extra:
        c=tuple(map(int,json.loads(f.read_text())["colors"][:len(Q)]))
        assert len(c)==len(Q) and set(c)==set(range(5))
        assert all(c[u]!=c[v] for u,v in E)
        banks.append(c)
    assert len(banks)<=64
    with a.output.open("w") as out:
        print(len(Q),len(D),len(banks),len(E),file=out)
        for row in Q+sorted(D)+banks:
            print(*row,file=out)
    print(f"Wrote {len(Q)} numerator rows, {len(D)} verified signed unit steps, {len(banks)} proper base palettes.")


if __name__=="__main__":main()

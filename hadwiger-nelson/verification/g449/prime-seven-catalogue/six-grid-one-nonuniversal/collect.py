#!/usr/bin/env python3
"""Audit complete sharded receipts, separating missed-point contact cases."""
from argparse import ArgumentParser
from collections import Counter
from pathlib import Path
import re

TAG=r"COMPLETE (\d+)/(\d+) generated (\d+) shard-incidences (\d+) retained (\d+) hubs (\d+) hubs4 (\d+) raw4 (\d+) eligible (\d+)"
NEXT=r"tested (\d+) (\d+) (\d+) residual (\d+) (\d+) (\d+)"
FIELDS=("generated","shard-incidences","retained","hubs","hubs4","raw4","eligible")


def main():
    p=ArgumentParser(description=__doc__)
    p.add_argument('work',type=Path)
    p.add_argument('shards',type=int)
    p.add_argument('--expect-closed',action='store_true')
    a=p.parse_args()
    assert a.shards>=16 and a.shards.bit_count()==1
    W=Counter()
    t=[0,0,0]
    r=[0,0,0]
    for i in range(a.shards):
        rows=(a.work/f'{i}.log').read_text().splitlines()
        assert len(rows)==2 and (m:=re.fullmatch(TAG,rows[0])) and (v:=re.fullmatch(NEXT,rows[1])), i
        shard,n,*counts=map(int,m.groups())
        assert (shard,n)==(i,a.shards)
        stat=dict(zip(FIELDS,counts))
        assert stat['generated']==3_852_576
        assert stat['retained']<=stat['shard-incidences'] and stat['hubs4']<=stat['hubs']<=stat['retained']
        assert stat['eligible']<=stat['raw4']
        tested=[int(g) for g in v.groups()[:3]]
        residual=[int(g) for g in v.groups()[3:]]
        assert all(t>=r for t,r in zip(tested,residual))
        for j in range(3):
            t[j]+=tested[j];r[j]+=residual[j]
        sets=set()
        cols=0
        with (a.work/f'{i}.residual').open() as f:
            for line in f:
                vs=list(map(int,line.split()))
                assert len(vs)==72 and all(-128<x<128 for x in vs)
                pts=tuple(tuple(vs[j:j+12]) for j in range(0,72,12))
                assert len(set(pts))==6 and pts not in sets
                sets.add(pts)
                cols+=1
        assert cols==sum(residual),i
        W.update(stat)
    assert (W['shard-incidences'],W['retained'],W['hubs'],W['hubs4'],W['raw4']) == (3_852_576,109_683,30_233,12_558,872_165)
    W.pop('generated')
    assert bool(sum(t)), "Empty completion scan is unexpected on the pinned inputs."
    print(f"Verified completeness receipts for all {a.shards} shards and all 3,852,576 incidences.")
    print(dict(W))
    print("Eligible six-point completions by 0/1/2 missed contacts:",t)
    print("Bank residuals by 0/1/2 missed contacts:",r)
    if a.expect_closed:
        assert a.shards==32 and W["eligible"]==83_818
        assert t==[3_833_277,145_271,33_796] and r==[0,0,0]


if __name__=='__main__':main()

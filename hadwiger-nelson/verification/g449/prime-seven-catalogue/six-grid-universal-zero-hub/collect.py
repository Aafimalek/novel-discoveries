#!/usr/bin/env python3
"""Collect complete serial shard receipts and audit residual line counts."""
from argparse import ArgumentParser
from collections import Counter
from pathlib import Path
import re

PAT = re.compile(r"COMPLETE (\d+)/(\d+) generated (\d+) shard-incidences (\d+) retained (\d+) hubs (\d+) hubs5 (\d+) raw5 (\d+) eligible (\d+) residual (\d+)")
FIELDS = ("generated","shard-incidences","retained","hubs","hubs5","raw5","eligible","residual")


def main():
    p=ArgumentParser(description=__doc__)
    p.add_argument('work',type=Path)
    p.add_argument('shards',type=int)
    p.add_argument('--expect-closed',action='store_true')
    a=p.parse_args()
    assert a.shards>=16 and a.shards.bit_count()==1
    W=Counter()
    hits=None
    for i in range(a.shards):
        with (a.work/f'{i}.log').open() as f:
            rows=f.read().splitlines()
        assert len(rows)==2 and (m:=PAT.fullmatch(rows[0])),i
        shard,n,*counts=map(int,m.groups())
        assert (shard,n)==(i,a.shards)
        stat=dict(zip(FIELDS,counts))
        assert stat['generated']==3_852_576
        assert stat['retained']<=stat['shard-incidences'] and stat['hubs5']<=stat['hubs']<=stat['retained']
        assert stat['residual']<=stat['eligible']<=stat['raw5']
        assert rows[1].startswith('first success counts:')
        c=list(map(int,rows[1].split(':',1)[1].split()))
        assert 35<=len(c)<=64 and sum(c)+stat['residual']==stat['eligible'] and all(j>=0 for j in c)
        if hits is None:hits=[0]*len(c)
        assert len(c)==len(hits)
        for j,num in enumerate(c):hits[j]+=num
        count=0
        with (a.work/f'{i}.residual').open() as f:
            for line in f:
                vs=list(map(int,line.split()))
                assert len(vs)==72 and all(-128<x<128 for x in vs)
                pts={tuple(vs[j:j+12]) for j in range(0,72,12)}
                assert len(pts)==6
                count+=1
        assert count==stat['residual'],i
        W.update(stat)
    assert W['shard-incidences']==3_852_576
    W.pop('generated')
    if a.expect_closed:
        assert a.shards==32
        assert W=={'shard-incidences':3852576,'retained':3656583,'hubs':3384633,
                  'hubs5':15638,'raw5':715925,'eligible':4578,'residual':0}
    print(f"Verified completeness receipts for all {a.shards} shards and all 3,852,576 incidences.")
    print(dict(W))
    print("First coverage palette counts:",hits)
    if W['residual']:
        print("Unresolved with this verified bank:",W['residual'])
    else:
        print("No residual degree-zero-hub configurations.")


if __name__=='__main__':main()

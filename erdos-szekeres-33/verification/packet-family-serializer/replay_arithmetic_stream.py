#!/usr/bin/env python3
"""Arithmetic ranks + exact streaming comparison for all emitted row families."""
from pathlib import Path
from itertools import combinations
from math import comb
import argparse

def sign_id(n,a,b,c):
    assert 0<=a<b<c<n
    t=b-a-1
    return comb(n,3)-comb(n-a,3)+t*(n-a-2)-t*(t-1)//2+c-b

class Side:
    def __init__(self,n,lim,cup,base):
        self.lim,self.cup,self.base=lim,cup,base
        self.pair_prefix,self.triple_prefix={},{}
        total=0
        for a,c in combinations(range(n),2):
            count=max(0,min(lim,c-a+1)-1)
            self.pair_prefix[a,c]=total
            total+=count
        self.pairs_size=total
        for a,b,c in combinations(range(n),3):
            count=max(0,min(lim,self.width(a,b,c))-3)
            self.triple_prefix[a,b,c]=total
            total+=count
        self.size=total

    def width(self,a,b,c):
        return (c-b if self.cup else b-a)+2

    def pair(self,d,a,c):
        assert 2<=d<=min(self.lim,c-a+1)
        return self.base+self.pair_prefix[a,c]+(d-2)+1

    def state(self,n,d,a,b,c):
        assert 3<=d<=min(self.lim,self.width(a,b,c))
        if d==3:
            return (1 if self.cup else -1)*sign_id(n,a,b,c)
        return self.base+self.triple_prefix[a,b,c]+(d-4)+1

    def rows(self,n):
        for a,c in combinations(range(n),2):
            yield (self.pair(2,a,c),)
            if self.lim<=c-a+1:
                yield (-self.pair(self.lim,a,c),)
            for d in range(3,min(self.lim,c-a+1)+1):
                yield (-self.pair(d,a,c),self.pair(d-1,a,c))
        for a,b,c in combinations(range(n),3):
            for d in range(3,min(self.lim,self.width(a,b,c))+1):
                x=self.state(n,d,a,b,c)
                yield (-x,self.pair(d,a,c))
                if d>=self.lim:
                    continue
                if self.cup:
                    for e in range(a):
                        yield (-x,-sign_id(n,e,a,b),self.state(n,d+1,e,a,c))
                else:
                    for e in range(c+1,n):
                        yield (-x,sign_id(n,b,c,e),self.state(n,d+1,a,c,e))

def cross(n,k,cap,cup):
    for a,c in combinations(range(n),2):
        for s in range(2,k+1):
            t=k+2-s
            if s<=min(cap.lim,c-a+1) and 2<=t<=min(cup.lim,c-a+1):
                yield (-cap.pair(s,a,c),-cup.pair(t,a,c))

def packet(n):
    for a,b,c,e in combinations(range(n),4):
        p,q,r,s=(sign_id(n,*x) for x in ((a,b,c),(a,b,e),(a,c,e),(b,c,e)))
        yield (-p,-s,q)
        yield (-q,-s,r)
        yield (-p,-r,q)
        yield (p,s,-q)
        yield (q,s,-r)
        yield (p,r,-q)

def compare(path,n,k,A,B):
    assert n>=3 and 2<=A and 2<=B
    cap=Side(n,A,False,comb(n,3))
    cup=Side(n,B,True,cap.base+cap.size)
    total_vars=cup.base+cup.size
    families=[('cap',cap.rows(n)),('cup',cup.rows(n)),('cross',cross(n,k,cap,cup)),
              ('packets',packet(n))]
    count=0
    spans={}
    with path.open('rb') as f:
        head=f.readline()
        parts=head.split()
        assert len(parts)==4 and parts[:2]==[b'p',b'cnf']
        v,clauses=map(int,parts[2:])
        assert total_vars==v
        assert head==f'p cnf {v} {clauses}\n'.encode('ascii')
        for name,rows in families:
            begin=count+1
            for r in rows:
                assert r and all(1<=abs(l)<=v for l in r)
                expected=(' '.join(map(str,r))+' 0\n').encode('ascii')
                count+=1
                got=f.readline()
                assert got==expected, (path,name,count,got,expected)
            spans[name]=(begin,count)
        assert count==clauses and f.readline()==b''
    assert spans['packets'][1]-spans['packets'][0]+1==6*comb(n,4)
    print(f'{path.name}: exact headers + {v} variables, {count} literal-identical ordered rows, EOF')
    print('  family sizes:',{name:hi-lo+1 for name,(lo,hi) in spans.items()})
    print('  dictionary sizes:',dict(sign=comb(n,3),cap_pair=cap.pairs_size,
         cap_triple=cap.size-cap.pairs_size,cup_pair=cup.pairs_size,cup_triple=cup.size-cup.pairs_size))
    print(f'  packet suffix = body rows {spans["packets"][0]}–{spans["packets"][1]}')

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('files',type=Path,nargs='+')
    p.add_argument('--n',type=int,default=32)
    p.add_argument('--k',type=int,default=7)
    p.add_argument('--cap',type=int,default=7)
    p.add_argument('--cup',type=int,default=6)
    a=p.parse_args()
    for path in a.files:
        compare(path,a.n,a.k,a.cap,a.cup)

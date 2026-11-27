"""Byte comparison for the closed state numbering in EulerNumberedCounters."""
from pathlib import Path
import sys

def slot(k,r,j):
    return 2*j+r if r < 2 else k*r+j

def seq(m,k,base,ids,sign):
    assert len(ids)==m+k
    s=lambda r,j: base+slot(k,r,j)
    l=lambda i: (-1 if sign else 1)*ids[i]
    C=[]
    for r in range(m):
        C.append((l(r),s(r,0)))
        for j in range(k):
            if r+1<m:
                C.append((-s(r,j),s(r+1,j)))
            if j+1<k:
                C.append((l(r+j+1),-s(r,j),s(r,j+1)))
            else:
                C.append((l(r+k),-s(r,j)))
    assert len({s(r,j) for r in range(m) for j in range(k)})==m*k
    return C

def projection():
    p=list(range(1297,1333))
    return seq(17,19,9073,p,False)+seq(19,17,9396,p,True)

def excess(g):
    p=[9719+42*g+7*a+j for a in range(6) for j in range(3,7)]
    return seq(5,19,9887+190*g,p,False)+seq(19,5,9982+190*g,p,True)

P=projection()
E=[c for g in range(4) for c in excess(g)]
assert len(P)==1292 and len(E)==1520
for orig in map(Path,sys.argv[1:]):
    got=[tuple(map(int,s.split()[:-1])) for s in orig.read_text('ascii').splitlines()[1:]]
    assert got[31752:31752+len(P)]==P
    pos=[i for i,c in enumerate(got) if c==E[0] and got[i:i+len(E)]==E]
    assert len(pos)==1
    print(orig,'projection 31753..33044',f'excess {pos[0]+1}..{pos[0]+len(E)}', 'all 2812 exact')

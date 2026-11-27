"""Seven normalized CNF branches for the size-17, minimum-degree-two case."""

from itertools import combinations, permutations, product
from pathlib import Path
import sys

from pysat.card import CardEnc
import anchored_base as base

case, path=sys.argv[1:]
diagrams={
 "double-same":((1,2,0,2),(2,2,2,0)),
 "double-cross1":((1,2,0,1),(2,2,2,2)),
 "double-cross2":((1,2,0,2),(2,2,2,1)),
 "q2":((1,2,0,2),(2,2,1,3)),
 "one":((1,2,0,2),(2,2,2,3)),
 "zero":((1,2,2,2),(2,2,3,3)),
}
words=diagrams.get(case,())
prefix=[max([1]+[w[i] for w in words])+1 for i in range(4)]
F,W,P,D=base.build_encoding(6,17,2,fixed_prefix=prefix)
v,gs=range(6),range(4)
cp=tuple(combinations(gs,2))

def p(i,j,a,b):
    return P[i,j,a,b] if i<j else P[j,i,b,a]

for word in W:
    F.append([p(i,j,word[i],word[j]) for i,j in cp])
for g in gs:
    F.extend(CardEnc.equals([D[g,a][d] for a in v for d in range(3,7)],
                            bound=5,top_id=F.nv).clauses)

if case=='allused':
    # An all-low word and five high labels in every group.
    for g in gs:
        F.append([-D[g,0][3]])
        for a in range(1,6):
            F.append([D[g,a][3]])
else:
    F.append([-D[1,2][3]])
    F.append([-p(0,1,0,2)])
    for w in words: F.append([W[w]])
    remainders = {
        "q2": (range(2,6),range(4,6)),
        "one": (range(3,6),range(4,6)),
        "zero": (range(4,6),range(4,6)),
    }
    left,right=remainders.get(case,(range(3,6),range(3,6)))
    for a,b in product(left,right):
        F.append([p(2,3,a,b)])
    for a in left:
        F.append([D[2,a][len(right)]])
    for b in right:
        F.append([D[3,b][len(left)]])
    if case=='q2':
        for d in range(3,7):
            F.append([-D[3,4][d],D[3,5][d]])

# Standard candidate rectangle cuts with known degree and one-neighbor overlap.
for i,j in cp:
    rem=tuple(sorted(set(gs)-{i,j}))
    for h,k in (rem,rem[::-1]):
        for a,b,c in product(v,repeat=3):
            for dx,dy in product(range(2,4),repeat=2):
                d=6-dx-dy
                edge=[p(i,j,a,b),p(i,h,a,c),p(j,h,b,c),D[i,a][dx+1],D[j,b][dy+1]]
                if d>2:
                    F.append([*edge,D[h,c][d]])
                if d+1>2:
                    for t in v:
                        F.append([*edge,-p(i,k,a,t),-p(j,k,b,t),D[h,c][d+1]])

# If an unused low-low pair has at least two common neighbors in one
# remaining group, the other group must have no common neighbor (4×3
# would require 6 degree excess), and such q2 overlaps occur only in
# the first branch of the partition.
if case!='allused':
    for i,j in cp:
        rem=tuple(sorted(set(gs)-{i,j}))
        for h,k in (rem,rem[::-1]):
            for a,b in product(v,repeat=2):
                allow=[p(i,j,a,b),D[i,a][3],D[j,b][3]]
                C=[[-p(i,h,a,t),-p(j,h,b,t)] for t in v]
                E=[[-p(i,k,a,t),-p(j,k,b,t)] for t in v]
                if case=='q2':
                    for r,t in combinations(v,2):
                        for u in v:
                            F.append([*allow,*C[r],*C[t],*E[u]])
                if case.startswith('double') or case=='one':
                    for r,t in combinations(v,2):
                        F.append([*allow,*C[r],*C[t]])
                if case=='one' and h<k:
                    for r,u in product(v,repeat=2):
                        F.append([*allow,*C[r],*E[u]])
                if case=='zero':
                    for r in v:
                        F.append([*allow,*C[r]])

# Sort free equal-frequency row/column incidence vectors as in the size-16
# proof. The reserved prefixes include all anchors and all q2 diagram labels
# whose ordering is separately fixed.
if case=='q2':
    prefix[3]=6
def tie(i,j,a):
    for first in v:
        L=[p(i,j,a,b) for b in range(first)]
        R=[p(i,j,a+1,b) for b in range(first)]
        for bits in product((False,True),repeat=first):
            common=[-x if b else x for V in (L,R) for x,b in zip(V,bits)]
            for d in range(2,7):
                hd=[D[i,a+1][d+1]] if d<6 else []
                F.append([-D[i,a][d],*hd,*common,-p(i,j,a,first),p(i,j,a+1,first)])
for a in range(prefix[0],5): tie(0,1,a)
for i in range(1,4):
    for a in range(prefix[i],5): tie(i,0,a)

F.to_file(path)
print(case, F.nv, len(F.clauses))

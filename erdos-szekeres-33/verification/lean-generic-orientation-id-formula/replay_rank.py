#!/usr/bin/env python3
"""Independent small arithmetic sanity check, not part of the Lean proof."""
from itertools import combinations
from math import comb
tot=0
for n in range(3,33):
    for expected,(a,b,c) in enumerate(combinations(range(n),3),1):
        first=sum(sum(n-j-1 for j in range(i+1,n)) for i in range(a))
        second=sum(n-j-1 for j in range(a+1,b))
        assert first==sum(comb(n-i-1,2) for i in range(a))
        assert expected==first+second+(c-b-1)+1
        tot+=1
print(f'Independent rank identity matched {tot} triples over all n=3..32.')

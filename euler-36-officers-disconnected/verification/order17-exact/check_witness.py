"""Check against all 1296 words in the 36-officer puzzle."""
from itertools import combinations,product
from pathlib import Path

W=tuple(tuple(map(int,line)) for line in
        Path(__file__).with_name("maximal-18-witness.txt").read_text().splitlines())
assert len(W)==len(set(W))==18
assert all(len(w)==4 and all(0<=a<6 for a in w) for w in W)
ij=tuple(combinations(range(4),2))
used={(i,j,w[i],w[j]) for w in W for i,j in ij}
assert len(used)==6*len(W)
assert all(any((i,j,w[i],w[j]) in used for i,j in ij)
           for w in product(range(6),repeat=4))
print("18 placements, pair-injective and maximal")

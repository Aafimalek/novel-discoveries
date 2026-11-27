"""Independently audit exact archived DIMACS core prefix against Lean formulas."""
from pathlib import Path
from itertools import product, combinations
import hashlib, sys
p = Path(sys.argv[1])
raw = p.read_bytes()
digest = hashlib.sha256(raw).hexdigest()
assert digest == '00b1bf0edffac4f5008c82475f22dff03a89dae040be0b268f2d6f28a63cea38'
h, *lines = raw.splitlines()
assert h == b'p cnf 10646 60567' and len(lines) == 60567
actual = []
for l in lines:
    v=tuple(map(int,l.split()))
    assert v[-1]==0 and all(0<abs(x)<=10646 for x in v[:-1])
    actual.append(v[:-1])
coords = tuple(combinations(range(4),2))
words = tuple(product(range(6),repeat=4))
pair_keys = tuple((i,j,a,b) for i,j in coords for a,b in product(range(6),repeat=2))
W = lambda w: 1+216*w[0]+36*w[1]+6*w[2]+w[3]
R = lambda i,j: j-1 if i==0 else j+1 if i==1 else 5
P = lambda p: 1297+36*R(*p[:2])+6*p[2]+p[3]
assert [W(w) for w in words] == list(range(1,1297))
assert [P(p) for p in pair_keys] == list(range(1297,1513))
expected = [tuple(P((i,j,w[i],w[j])) for i,j in coords) for w in words]
for q, (i,j,a,b) in enumerate(pair_keys):
    pair = P((i,j,a,b))
    x = [W(w) for w in words if w[i]==a and w[j]==b]
    assert len(x)==36
    s = list(range(1513+35*q,1513+35*(q+1)))
    expected.append((-pair,*x))
    expected.extend((-z,pair) for z in x)
    expected.append((-x[0],s[0]))
    for r in range(35):
        if r<34:
            expected.append((-s[r],s[r+1]))
        expected.append((-x[r+1],-s[r]))
        if r<34:
            expected.append((-x[r+1],s[r+1]))
assert len(expected)==1296+216*(1+36+104)==31752
for i,(got,want) in enumerate(zip(actual,expected),start=1):
    assert got==want,(i,got,want)
print(f'{digest}  {p.name}')
print('31,752 exact prefix clauses match, including all 216 sequential counters')
print('Covered variable blocks: words 1..1296, pairs 1297..1512, support AMO auxiliary states 1513..9072')
print(f'Uncovered trailing clauses: {len(actual)-len(expected):,}')

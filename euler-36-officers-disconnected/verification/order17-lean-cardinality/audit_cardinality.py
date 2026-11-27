"""Match the physical projection and four degree-excess counter blocks."""
from pathlib import Path
import hashlib,sys

file = Path(sys.argv[1]); data = file.read_bytes()
dig = hashlib.sha256(data).hexdigest()
assert dig == '00b1bf0edffac4f5008c82475f22dff03a89dae040be0b268f2d6f28a63cea38'
header, *rest = data.splitlines()
assert header == b'p cnf 10646 60567' and len(rest)==60567
actual = [tuple(map(int,line.split()[:-1])) for line in rest]

def sequential(x, k, last):
    out = []
    states = {}
    m = len(x)-k
    def s(r,j):
        nonlocal last
        if (r,j) not in states:
            last+=1
            states[r,j]=last
        return states[r,j]
    for r in range(m):
        out.append((-x[r], s(r,0)))
        for j in range(k):
            here=s(r,j)
            if r+1<m:
                out.append((-here,s(r+1,j)))
            if j+1<k:
                out.append((-x[r+j+1],-here,s(r,j+1)))
            else:
                out.append((-x[r+k],-here))
    assert len(states)==m*k
    return out,last

def exact(x,k,last):
    low, mid = sequential([-i for i in x], len(x)-k, last)
    high, end = sequential(x,k,mid)
    return low+high,mid,end

start=31752
projection, mid, end = exact(list(range(1297,1333)),17,9072)
assert (mid,end)==(9395,9718) and len(projection)==1292
assert actual[start:start+len(projection)]==projection
print(f'SHA-256: {dig}')
print(f'Exact-17 projection cardinality: clauses {start+1}–{start+len(projection)}, auxiliaries 9073–{end} (split at {mid})')

# Each degree bit is next in the base IDPool: 24 labels, each with
# seven unary, degree-at-least threshold bits. Select thresholds 3..6.
last=9886
excess=[]
for g in range(4):
    bits = [9719+7*(6*g+a)+d for a in range(6) for d in range(3,7)]
    assert len(bits)==24
    shape, middle, newlast = exact(bits,5,last)
    print(f'Group {g}: supplemental exact-5 excess, auxiliaries {last+1}–{newlast} (split at {middle})')
    excess.extend(shape)
    last=newlast
assert last==10646
occurrences=[i for i,c in enumerate(actual) if c==excess[0]]
positions=[i for i in occurrences if actual[i:i+len(excess)]==excess]
assert len(positions)==1, positions
i=positions[0]
print(f'Four exact-5 excess blocks combined: clauses {i+1}–{i+len(excess)} ({len(excess)} clauses)')
print(f'All auxiliary counter clauses audited: {len(projection)+len(excess)}')

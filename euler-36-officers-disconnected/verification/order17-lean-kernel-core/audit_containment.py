"""Verify each extracted core's inclusion as a multiset of normalized clauses."""
from collections import Counter
import hashlib
from pathlib import Path
import sys

def clauses(path):
    texts = Path(path).read_text().splitlines()
    var_count = count = None
    result = Counter()
    for line in texts:
        line = line.strip()
        if not line or line.startswith("c"):
            continue
        if line.startswith("p"):
            p, k, n, m = line.split()
            assert p == 'p' and k == 'cnf' and var_count is None
            var_count, count = int(n), int(m)
            continue
        xs = tuple(map(int,line.split()))
        assert xs[-1] == 0 and all(0 < abs(x) <= var_count for x in xs[:-1])
        result[tuple(sorted(xs[:-1]))] += 1
    assert result.total() == count
    return result

names=sys.argv[1:] or ["original.cnf","core.cnf"]
assert len(names) >= 2, "pass the archived original and at least one core"
expected = "00b1bf0edffac4f5008c82475f22dff03a89dae040be0b268f2d6f28a63cea38"
observed = hashlib.sha256(Path(names[0]).read_bytes()).hexdigest()
assert observed == expected, f"unexpected original SHA-256 {observed}"
print(f"{names[0]}: SHA-256 {observed}")
for a,b in zip(names,names[1:]):
    bigger,smaller=clauses(a),clauses(b)
    missing=smaller-bigger
    assert not missing, missing
    print(f"{b}: all {smaller.total()} clauses belong to {a} ({bigger.total()} clauses)")

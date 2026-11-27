from math import comb
from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).parent / "upstream"))
from lib.erdos import etv_signotope
from signotope_cnf import generate
scope = ((8,5), (9,5), (16,6), (17,6), (33,7))
for n,k in scope:
    f = Path(f"dp-{n}-{k}.cnf")
    F = etv_signotope(k,k,k,n)
    F.write(f)
    print(f"DP {n} {k} {F._num_vars} {len(F._clauses)} {f.stat().st_size}")
    if n != 33:
        f = Path(f"compact-{n}-{k}.cnf")
        v,c = generate(n,k,f)
        print(f"compact {n} {k} {v} {c} {f.stat().st_size}")
    else:
        v=comb(n,3)+comb(n,4)
        c=8*comb(n,4)+comb(n,k)
        print(f"compact {n} {k} {v} {c} not_generated")

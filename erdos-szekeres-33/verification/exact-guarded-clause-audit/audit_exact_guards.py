#!/usr/bin/env python3
"""Compare the actual numbered 32-label CNF with quantified guarded clauses.

Executable independent finite audit, not a Lean theorem. No SAT solver.
Only the inverse variable layout is shared by contractual definition;
expected row order is deliberately unrelated to upstream generation order.
"""
from argparse import ArgumentParser
from collections import Counter
from hashlib import sha256
from itertools import combinations, product
from pathlib import Path
import subprocess
import tempfile

N, K, A, B = 32, 7, 7, 6
LIMIT = {"cap": A, "cup": B}
VERS = range(N)
PAIRS = tuple(combinations(VERS, 2))
TRIPLES = tuple(combinations(VERS, 3))
QUARTETS = tuple(combinations(VERS, 4))
PINNED = "7f79b4e0e4186450489292b4cf823b75b0d85e7c70cae14d4ab0fbbf61cccd95"

def pair_fits(a,c,d):
    return a<c and 2<=d<=c-a+1

def state_fits(side,a,b,c,d):
    a0,c0 = (a,b) if side=="cap" else (b,c)
    return a<b<c and 3<=d<=c0-a0+2

def signed_layout():
    table = [("sign",a,b,c) for a,b,c in TRIPLES]
    for s,h in LIMIT.items():
        for a,c in PAIRS:
            table.extend((s,"pair",d,a,c) for d in range(N+1) if d<=h and pair_fits(a,c,d))
        for a,b,c in TRIPLES:
            table.extend((s,"state",d,a,b,c) for d in range(N+1) if 4<=d<=h and state_fits(s,a,b,c,d))
    m={x:i for i,x in enumerate(table,1)}
    assert len(m)==len(table)==37365
    return m

def expected():
    id=signed_layout()
    def sign(a,b,c):
        return id[("sign",a,b,c)]
    def pair(s,d,a,c):
        return id[(s,"pair",d,a,c)]
    def state(s,d,a,b,c):
        if d==3:
            return (-1 if s=="cap" else 1)*sign(a,b,c)
        return id[(s,"state",d,a,b,c)]
    # Quantify first by OUTER pair, then color and length, not production order.
    for a,c in PAIRS:
        for s,h in LIMIT.items():
            yield s+" base pair",(pair(s,2,a,c),)
            if pair_fits(a,c,h):
                yield s+" threshold",(-pair(s,h,a,c),)
            for d in range(2,h):
                if pair_fits(a,c,d+1):
                    yield s+" shorten",(-pair(s,d+1,a,c),pair(s,d,a,c))
        # Quantify both lengths independently, then impose s+t=K+2.
        for i,j in product(range(2,A+1),range(2,B+1)):
            if i+j==K+2 and pair_fits(a,c,i) and pair_fits(a,c,j):
                yield "opposite",(-pair("cap",i,a,c),-pair("cup",j,a,c))
    # Length-three initial cap/cup implications are tautologies after
    # aliases; no fresh variables or nontrivial rows belong to that family.
    for a,b,c in TRIPLES:
        for s,h in LIMIT.items():
            for d in range(3,h+1):
                if state_fits(s,a,b,c,d):
                    yield s+" project",(-state(s,d,a,b,c),pair(s,d,a,c))
    # Both sides use the same quadruple loop, with entirely different old
    # source triples and polarity. Fits tests refer only to the source
    # while checked arithmetic ensures every destination is an allocated key.
    for a,b,c,e in QUARTETS:
        for d in range(3,A):
            if state_fits("cap",a,b,c,d):
                yield "cap extend",(-state("cap",d,a,b,c),sign(b,c,e),state("cap",d+1,a,c,e))
        for d in range(3,B):
            if state_fits("cup",b,c,e,d):
                yield "cup extend",(-state("cup",d,b,c,e),-sign(a,b,c),state("cup",d+1,a,b,e))
        names = sign(a,b,c),sign(a,b,e),sign(a,c,e),sign(b,c,e)
        for outer_l,middle,outer_r in ((0,1,3),(1,2,3),(0,1,2)):
            for t in (1,-1):
                yield "packet",(-t*names[outer_l],-t*names[outer_r],t*names[middle])

def packet_check():
    for v in product((False, True),repeat=4):
        tri=((0,1,3),(1,2,3),(0,1,2))
        sat=all(v[x]!=t or v[z]!=t or v[y]==t for x,y,z in tri for t in (False,True))
        assert sat==(sum(x!=y for x,y in zip(v,v[1:]))<=1)

def canonical(lits):
    assert 1<=len(lits)<=3 and len(lits)==len(set(lits))
    return ",".join(map(str,sorted(lits)))+"\n"

def run(input_cnf):
    packet_check()
    h=sha256()
    cnt=lit=0
    with tempfile.TemporaryDirectory() as tmp:
        actual=Path(tmp)/"actual"; wanted=Path(tmp)/"wanted"
        with input_cnf.open("rb") as f,actual.open("w") as out:
            row=f.readline(); h.update(row)
            assert row==b"p cnf 37365 474144\n"
            for row in f:
                h.update(row)
                vals=list(map(int,row.split()))
                assert vals[-1]==0 and all(0<abs(x)<=37365 for x in vals[:-1])
                out.write(canonical(vals[:-1]))
                cnt+=1; lit+=len(vals)-1
        assert (cnt,lit,h.hexdigest())==(474144,1375738,PINNED)
        counts=Counter()
        with wanted.open("w") as out:
            for family,row in expected():
                counts[family]+=1
                out.write(canonical(row))
        assert sum(counts.values())==cnt
        tmp=Path(tmp)
        for f in actual,wanted:
            with (tmp/(f.name+".sorted")).open("wb") as out:
                subprocess.run(["sort","-S","8M","--parallel=1","-T",str(tmp),str(f)],stdout=out,check=True)
        # cmp comparison is byte-for-byte, not a digest tie-break.
        subprocess.run(["cmp",str(tmp/"actual.sorted"),str(tmp/"wanted.sorted")],check=True)
    print("Exact guarded row multiset equals pinned target CNF (up to clause/literal order).")
    for k,v in sorted(counts.items()): print(k,v)
    print("Variables 37365; clauses 474144; literals 1375738; no solver.")
    print("All 16 packet assignments satisfy these six clauses iff they are monotone.")

if __name__=="__main__":
    p=ArgumentParser(description=__doc__)
    p.add_argument("formula",type=Path)
    run(p.parse_args().formula)

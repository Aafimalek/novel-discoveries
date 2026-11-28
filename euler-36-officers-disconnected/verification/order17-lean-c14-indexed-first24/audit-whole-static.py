#!/usr/bin/env python3
"""Static C14 audit. Not a Lean proof; no solver and no persistent proof objects."""
import argparse
from collections import Counter
import gzip
import hashlib
import json
from pathlib import Path

p = argparse.ArgumentParser()
p.add_argument('core', type=Path)
p.add_argument('trace', type=Path)
p.add_argument('out', type=Path)
a = p.parse_args()
a.out.mkdir(exist_ok=True, parents=True)
assert a.core.stat().st_size <= 1024*1024 and a.trace.stat().st_size <= 8*1024*1024
h = hashlib.sha256()
rows = {}
with a.core.open('rb') as f:
    head = f.readline(); h.update(head)
    header = head.split()
    assert header == [b'p', b'cnf', b'10646', b'8825']
    vs, n = map(int, header[2:])
    for idx, line in enumerate(f, 1):
        h.update(line)
        lits = tuple(map(int, line.split()))
        assert lits and lits[-1] == 0 and all(0 < abs(x) <= vs for x in lits[:-1])
        rows[idx] = lits[:-1]
assert len(rows) == n
core_hash = h.hexdigest()
live = set(rows)
additions = []
ordinal = {}
dep = {}
dels = rup_units = 0
hint_hist = Counter()
wid_hist = Counter()
h = hashlib.sha256()
with a.trace.open('rb') as f:
    end = 0
    for lineno, line in enumerate(f, 1):
        start = end; end += len(line); h.update(line)
        assert end <= 8*1024*1024 and line.endswith(b'\n')
        tokens = line.split()
        if tokens[1] == b'd':
            dd = list(map(int, tokens[2:]))
            assert dd[-1] == 0 and len(set(dd[:-1])) == len(dd)-1 and set(dd[:-1]) <= live, lineno
            live.difference_update(dd[:-1]); dels += len(dd)-1
            continue
        ts = tuple(map(int, tokens)); z = ts.index(0)
        i, r, hints = ts[0], ts[1:z], ts[z+1:-1]
        assert i > n and i not in rows and (not additions or i > additions[-1][0]) and ts[-1] == 0, lineno
        assert all(0 < abs(x) <= vs for x in r) and hints and all(x in live for x in hints), (lineno, i)
        false = set(r)
        for t, hid in enumerate(hints):
            remain = [x for x in rows[hid] if x not in false]
            if t+1 == len(hints):
                assert not remain, (lineno, i, hid, remain)
            else:
                assert len(remain) == 1, (lineno, i, hid, remain)
                false.add(-remain[0]); rup_units += 1
        rows[i] = r; live.add(i)
        dep[i] = hints; ordinal[i] = len(additions)
        additions.append((i, start, end, lineno))
        hint_hist[len(hints)] += 1
        wid_hist[len(r)] += 1
assert end == a.trace.stat().st_size
empty = additions[-1][0]; assert rows[empty] == () and empty in live
trace_hash = h.hexdigest()
# Backward dependency cone rooted at empty. No included hint depends on
# an omitted addition. All source and target IDs have fixed rows globally.
marked = {empty}
for i, _, _, _ in reversed(additions):
    if i in marked:
        marked.update(dep[i])
assert all(i in marked for i in dep[empty])
active_adds = [x for x in additions if x[0] in marked]
assert active_adds[-1][0] == empty
# Last use in the projected trace. Virtual one-past-end use retains empty.
m = len(active_adds); last = {empty:m}; born = {}
for j,(i,_,_,_) in enumerate(active_adds):
    born[i] = j
    for k in dep[i]:
        last[k] = j
assert set(last) == marked
# Cut j is the point just before the addition with projected index j.
# For exact cross-frontier, keep born < j <= last (originals born at -1).
expiry = {}
for i, j in last.items():
    expiry.setdefault(j, []).append(i)
required = {}
for cap in [24, 64, 128, 256, 512]:
    required[cap] = {0,*range(cap,m,cap),m}
need_cuts = set.union(*required.values())
pool = set(i for i in marked if i <= n)
states = {0: tuple(sorted(pool))}
for j,(i,*_) in enumerate(active_adds):
    pool.add(i)
    for k in expiry.get(j, []):
        pool.remove(k)
    if j+1 in need_cuts:
        states[j+1] = tuple(sorted(pool))
assert states[m] == (empty,)
# Explicit exact frontier IDs and exact local incoming hint IDs for every
# chunk. Clause values are in canonical original or learned numbering below.
def write_gz(path, obj):
    with path.open('wb') as out, gzip.GzipFile(filename='',mode='wb',fileobj=out,mtime=0) as gz:
        gz.write((json.dumps(obj,separators=(',',':'))+'\n').encode())

plans = []
for cap, cuts in required.items():
    cuts = sorted(cuts)
    chunks = []
    for lo,hi in zip(cuts,cuts[1:]):
        pre = states[lo]; post = states[hi]
        origins = [x[0] for x in active_adds[lo:hi]]
        stepped = set(origins)
        local_imports = sorted({k for i in origins for k in dep[i] if k not in stepped})
        local_exports = sorted(stepped.intersection(post))
        assert set(local_imports).issubset(pre) and set(post).issubset(set(pre) | stepped)
        for cut, state in [(lo, pre), (hi, post)]:
            assert all(born.get(i,-1) < cut <= last[i] for i in state)
        chunks.append(dict(lo=lo,hi=hi,first_id=origins[0],last_id=origins[-1],
                           first_byte=active_adds[lo][1],past_last_byte=active_adds[hi-1][2],
                           pre=list(pre),post=list(post), local_imports=local_imports,
                           local_exports=local_exports,
                           hints=sum(len(dep[i]) for i in origins),
                           max_hints=max(len(dep[i]) for i in origins),
                           max_literals=max(len(rows[i]) for i in origins)))
    write_gz(a.out/f'frontiers-{cap}.json.gz',chunks)
    fields = ['pre','post','local_imports','local_exports']
    plans.append(dict(slice=cap,chunks=len(chunks),
                      max={x:max(len(c[x]) for c in chunks) for x in fields},
                      median={x:sorted(len(c[x]) for c in chunks)[len(chunks)//2] for x in fields},
                      max_hints_per_chunk=max(c['hints'] for c in chunks),
                      max_single_hints=max(c['max_hints'] for c in chunks),
                      max_single_literals=max(c['max_literals'] for c in chunks)))

write_gz(a.out/'exact-cone.json.gz',dict(
    orig=[(i,rows[i]) for i in sorted(x for x in marked if x<=n)],
    learned=[dict(id=i,original_ordinal=ordinal[i]+1, clause=rows[i],hints=dep[i],
                  begin=s,end=e,line=l)
             for i,s,e,l in active_adds]))
report = dict(cnf_sha256=core_hash,lrat_sha256=trace_hash,trace_bytes=end,
              variables=vs,original_clauses=n,trace_lines=lineno,deletions=dels,
              total_rup_units=rup_units,additions=len(additions),
              max_hints=max(hint_hist),max_literals=max(wid_hist),
              terminal_empty_id=empty,cone_learned=m,cone_original=len(marked)-m,
              cone_hints=sum(len(dep[i]) for i,*_ in active_adds),
              plans=plans)
(a.out/'summary.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))

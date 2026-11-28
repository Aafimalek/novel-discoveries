#!/usr/bin/env python3
"""Independently drive a cap proof from its mathematical source and compare every archived result."""
from collections import Counter
from contextlib import redirect_stdout
import argparse
import hashlib
import importlib
import io
from pathlib import Path
import resource
import signal
import sys

if not __debug__:
    raise SystemExit("Run without Python optimization: proof checks use assertions.")

p = argparse.ArgumentParser(description=__doc__)
p.add_argument("packet", type=Path)
p.add_argument("cap", type=int)
p.add_argument("count", type=int)
p.add_argument("--max-depth", type=int, default=4)
args = p.parse_args()
base = args.packet.resolve()
sys.path.insert(0, str(base))
ck = importlib.import_module("checkpoint")
proof = importlib.import_module(f"anchored{args.cap}")
profiles, manifest = ck.load(base / "checkpoint")
assert manifest["cap"] == args.cap and manifest["x8_lower"] == args.cap
ids = [s["id"] for s in manifest["shards"]]
assert len(ids) == len(set(ids)) == args.count
signal.alarm(35)
fresh = ck.compute()
signal.alarm(0)
assert ck.dump(fresh) == ck.dump(profiles)
m_hash = hashlib.sha256(ck.dump(manifest)).hexdigest()
depth_counts = Counter()
seen_path = set()
for part in manifest["shards"]:
    name, a = part["id"], part["a"]
    seed = fresh[str(a)][part["lo"]:part["hi"]]
    assert hashlib.sha256(ck.dump(seed)).hexdigest() == part["input_sha256"]
    rows = ck.check_profiles(seed, 2)
    in_hash = part["input_sha256"]
    signal.alarm(35)
    for k in range(3, args.max_depth + 1):
        with redirect_stdout(io.StringIO()):
            nxt = proof.refine(args.cap, {a: rows}, k).get(a, [])
        ck.check_profiles(nxt, k)
        out_hash = hashlib.sha256(ck.dump(nxt)).hexdigest()
        record = {"id":name, "a":a, "depth":k, "manifest_sha256":m_hash,
                  "input_sha256":in_hash, "count":len(nxt),
                  "residual_sha256":out_hash, "residual":nxt}
        path = base / "progress" / f"{name}-d{k}.json"
        assert path.read_bytes() == ck.dump(record), f"Fresh result differs: {path.name}"
        seen_path.add(path.name)
        rows, in_hash = nxt, out_hash
        if not rows:
            break
    signal.alarm(0)
    assert not rows, f"Open shard after depth {args.max_depth}: {name}"
    depth_counts[k] += 1
assert set(x.name for x in (base / "progress").glob("*.json")) == seen_path
print("Manifest SHA256",m_hash)
print("Independent replay matches every saved result:",len(seen_path),"records")
print("Cleared shards:",args.count,"of",args.count)
print("Cleared counts by depth:",sorted(depth_counts.items()))
print("Peak RSS (KiB):", resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)

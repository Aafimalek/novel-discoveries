"""Merge f385 output files into one summary.

Usage: python aggregate.py OUT.json FILE [FILE ...]

Each input file covers a disjoint range [lo, hi). The merged summary has every
exception (G(n) = 0), the largest n with 0 <= G(n) <= t for each t, counts of
G(n) == t when the inputs have them, and per-dyadic-range minima of G(n) and
G(n)/sqrt(n). It also checks that the ranges tile one interval with no gaps.
"""
import json
import re
import sys

out_path, files = sys.argv[1], sys.argv[2:]
ranges, bad, last, count, rng = [], {}, {}, {}, {}
for path in files:
    text = open(path, encoding="utf-8").read()
    run = re.search(r"^RUN lo=(\d+) hi=(\d+)", text, re.M)
    if not run or "RANGE" not in text:
        sys.exit(f"incomplete output: {path}")
    ranges.append((int(run.group(1)), int(run.group(2))))
    for n, g in re.findall(r"^BAD (\d+) (-?\d+)$", text, re.M):
        bad[int(n)] = int(g)
    for t, n in re.findall(r"^LAST (\d+) (-?\d+)$", text, re.M):
        last[int(t)] = max(last.get(int(t), -1), int(n))
    for t, c in re.findall(r"^COUNT (\d+) (\d+)$", text, re.M):
        count[int(t)] = count.get(int(t), 0) + int(c)
    for k, g, ng, ratio, nr in re.findall(
        r"^RANGE (\d+) (-?\d+) (\d+) ([-\d.]+) (\d+)$", text, re.M
    ):
        k = int(k)
        cur = rng.setdefault(k, [None, None, None, None])
        if cur[0] is None or int(g) < cur[0]:
            cur[0], cur[1] = int(g), int(ng)
        if cur[2] is None or float(ratio) < cur[2]:
            cur[2], cur[3] = float(ratio), int(nr)

ranges.sort()
for (a, b), (c, d) in zip(ranges, ranges[1:]):
    if b != c:
        sys.exit(f"gap or overlap between [{a},{b}) and [{c},{d})")
summary = {
    "lo": ranges[0][0],
    "hi": ranges[-1][1],
    "files": len(files),
    "exceptions": sorted(n for n, g in bad.items() if g <= 0),
    "last_le": {t: last[t] for t in sorted(last)},
    "count_eq": {t: count[t] for t in sorted(count)},
    "dyadic": {
        k: {"min_G": v[0], "n_min_G": v[1], "min_ratio": v[2], "n_min_ratio": v[3]}
        for k, v in sorted(rng.items())
    },
}
json.dump(summary, open(out_path, "w"), indent=1)
print(f"[{summary['lo']}, {summary['hi']}) from {len(files)} files;",
      f"{len(summary['exceptions'])} exceptions, largest",
      max(summary["exceptions"], default=None))

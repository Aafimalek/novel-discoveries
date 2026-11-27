"""Deterministically regenerate the exact case CNFs without running a solver."""

from pathlib import Path
import sys

CASES = {
    "m1": ("certify.py", "1", [], "exact-f16-m1"),
    "m2-p1-h6": ("split.py", "2", ["1:6"], "proof-f16-m2-1:6"),
    "m2-p2-h5": ("split.py", "2", ["2:5"], "proof-f16-m2-2:5"),
    "m2-p2-h4": ("lowpair.py", "2", ["2:4"], "lowpair-f16-m2-2:4"),
    "m2-p3-h4": ("lowpair.py", "2", ["3:4"], "lowpair-f16-m2-3:4"),
    "m2-p4-h3-same": ("wedgefinal.py", "2", ["4:3", "same"], "wedgefinal-f16-m2-4:3-same"),
    "m2-p4-h3-cross1": ("wedgefinal.py", "2", ["4:3", "cross1"], "wedgefinal-f16-m2-4:3-cross1"),
    "m2-p4-h3-cross2": ("wedgefinal.py", "2", ["4:3", "cross2"], "wedgefinal-f16-m2-4:3-cross2"),
    "m2-p4-h3-zero": ("nodouble.py", "2", ["4:3", "zero"], "nodouble-f16-m2-4:3-zero"),
    "m2-p4-h3-one": ("nodouble.py", "2", ["4:3", "one"], "nodouble-f16-m2-4:3-one"),
    "m2-p4-h3-broad": ("lowpair.py", "2", ["4:3"], "lowpair-f16-m2-4:3"),
}

if len(sys.argv) != 3 or sys.argv[1] not in CASES:
    raise SystemExit(f"Usage: {sys.argv[0]} CASE OUTPUT\nCASES: {', '.join(CASES)}")
name, output = sys.argv[1:]
source, minimum, extra, _ = CASES[name]
source = Path(__file__).with_name(source)
code = source.read_text().split("\nwith Solver(", maxsplit=1)[0]
sys.argv = [source.name, "16", minimum, "cnf-only", *extra]
context = {"__file__": str(source), "__name__": "__main__"}
exec(compile(code, str(source), "exec"), context)
context["F"].to_file(output)

"""Compare Lean's actual numbered degree block against archived formulas.

Usage: python3 audit_degrees.py lean-block.txt NAME=original.cnf ...
"""
from pathlib import Path
from sys import argv
import hashlib

block = Path(argv[1]).read_bytes().splitlines()
assert len(block) == 6888
for arg in argv[2:]:
    name, path = arg.split("=", 1)
    data = Path(path).read_bytes()
    header, *orig = data.splitlines()
    assert header.startswith(b"p cnf 10646 ")
    assert orig[33046:39934] == block, name
    print(f"{name}: {len(block)} exact clauses (33047..39934), SHA256={hashlib.sha256(data).hexdigest()}")

#!/usr/bin/env python3
"""Check the extracted CNF is literally a clause submultiset of the original."""
from collections import Counter
from pathlib import Path
import sys


def read_dimacs(path):
    header = None
    clause = []
    records = []
    for row in Path(path).read_text("ascii").splitlines():
        columns = row.split()
        if not columns or columns[0] == "c":
            continue
        if columns[0] == "p":
            assert header is None and columns[1] == "cnf"
            header = tuple(map(int, columns[2:]))
            continue
        for i in map(int, columns):
            if i != 0:
                assert 0 < abs(i) <= header[0]
                clause.append(i)
            else:
                records.append(tuple(sorted(clause)))
                clause.clear()
    assert header is not None and not clause and len(records) == header[1]
    return Counter(records), header


if __name__ == "__main__":
    original, (n, total) = read_dimacs(sys.argv[1])
    core, (ncore, used) = read_dimacs(sys.argv[2])
    assert ncore == n and not (core - original)
    print(f"{used} exact core clauses are a submultiset of {total}; {n} original variable IDs")

#!/usr/bin/env python3
"""Put each extracted clause back in the exact literal order in the original."""
from collections import defaultdict, deque
from pathlib import Path
import sys


def read(path):
    data = Path(path).read_text(encoding="ascii").splitlines()
    head = data[0].split()
    assert head[:2] == ["p", "cnf"]
    number, size = map(int, head[2:])
    clauses = [tuple(map(int, l.split())) for l in data[1:]]
    assert len(clauses) == size
    assert all(c[-1] == 0 and all(0 < abs(i) <= number for i in c[:-1]) for c in clauses)
    return number, clauses


def restore(original, extracted, output):
    n, fc = read(original)
    n2, cc = read(extracted)
    assert n == n2
    rows = defaultdict(deque)
    for i, c in enumerate(fc):
        rows[tuple(sorted(c))].append(i)
    restored = [fc[rows[tuple(sorted(c))].popleft()] for c in cc]
    with open(output, "w", encoding="ascii") as out:
        print("p", "cnf", n, len(restored), file=out)
        for c in restored:
            print(*c, file=out)


if __name__ == "__main__":
    restore(*sys.argv[1:])

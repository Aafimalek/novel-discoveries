"""Exact checker for the one-source, four-isolate trace reduction."""

from collections import Counter
from itertools import combinations

POINTS = range(4)
TRACES = range(1 << len(POINTS))
MANDATORY = frozenset(t for t in TRACES if t.bit_count() >= 3)
OPTIONAL = tuple(t for t in TRACES if t not in MANDATORY)


def union_closed(family):
    return all((a | b) in family for a in family for b in family)


def max_chain_over(family, support):
    """Length of the longest strict chain with first member covering support."""
    lengths = {}
    for trace in sorted(family, reverse=True):
        lengths[trace] = 1 + max(
            (length for above, length in lengths.items() if (trace & above) == trace),
            default=0,
        )
    return max(
        (length for trace, length in lengths.items() if (trace & support) == support),
        default=0,
    )


def union_all(traces):
    support = 0
    for trace in traces:
        support |= trace
    return support


def analyze():
    stats = Counter()
    survivors = []
    for bits in range(1 << len(OPTIONAL)):
        family = MANDATORY | frozenset(
            trace for i, trace in enumerate(OPTIONAL) if bits & (1 << i)
        )
        freqs = tuple(sum(bool(t & (1 << i)) for t in family) for i in POINTS)
        # By relabeling, isolate 0 is the below-half point.
        if 2 * freqs[0] >= len(family) or not union_closed(family):
            continue
        stats["eligible"] += 1
        safe = [t for t in TRACES if all((t | r) in family for r in family)]
        metrics = []
        for i, j in combinations(POINTS, 2):
            banned = (1 << i) | (1 << j)
            support = union_all(t for t in safe if not (t & banned))
            surplus = freqs[i] + freqs[j] - len(family)
            chain = max_chain_over(family, support)
            metrics.append((i, j, support.bit_count(), surplus, chain))
        if any(surplus > s and chain >= 4 for _, _, s, surplus, chain in metrics):
            stats["excluded"] += 1
        else:
            survivors.append((family, freqs, metrics))
    return stats, survivors


if __name__ == "__main__":
    stats, survivors = analyze()
    assert stats == {"eligible": 106, "excluded": 105}, stats
    assert len(survivors) == 1, survivors
    family, freqs, metrics = survivors[0]
    assert family == frozenset(TRACES) - {1}, family
    assert freqs == (7, 8, 8, 8), freqs
    print(f"{stats['eligible']} eligible trace families; {stats['excluded']} excluded")
    print("Only survivor: all four-isolate traces except {0}; frequencies", freqs)
    print("Pair metrics (first, second, support size, surplus, chain length):")
    for row in metrics:
        print(row)

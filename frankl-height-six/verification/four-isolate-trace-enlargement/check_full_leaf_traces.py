"""Exact finite cuts for the four-isolate single-source residual."""
from itertools import combinations, permutations

ISOLATES = range(4)
TRACES = tuple(t for t in range(16) if t != 1)
INDEX = {t: i for i, t in enumerate(TRACES)}
TRACE_MASKS = [
    sum(1 << i for i, t in enumerate(TRACES) if t & (1 << v))
    for v in ISOLATES
]
TOP_MASK = (1 << INDEX[14]) | (1 << INDEX[15])
UPSETS_CONTAINING = [
    sum(1 << i for i, t in enumerate(TRACES) if (t & u) == u)
    for u in TRACES
]
X_ONE_HIGH = {3, 5, 9}


def is_useful_addition(added):
    size = added.bit_count()
    # x needs relief of one, while each high isolate has slack of one.
    return (
        2 * (added & TRACE_MASKS[0]).bit_count() + 1 <= size
        and all(2 * (added & TRACE_MASKS[v]).bit_count() <= size + 1
                for v in (1, 2, 3))
    )


def frequency_obstruction(safe):
    """Find a 0/1 weighting of the high isolates with impossible frequencies."""
    for high_subset in (2, 4, 6, 8, 10, 12, 14):
        total_weight = high_subset.bit_count()
        min_x = min((t & high_subset).bit_count() for t in safe if t & 1)
        min_nonempty_non_x = min(
            (t & high_subset).bit_count() for t in safe if t and not (t & 1)
        )
        if min_x + min_nonempty_non_x >= total_weight:
            return True
    return False


def canonical_family(family):
    def relabel(trace, labels):
        return (trace & 1) | sum(
            ((trace >> old) & 1) << new for old, new in zip((1, 2, 3), labels)
        )
    return min(
        tuple(sorted(relabel(trace, labels) for trace in family))
        for labels in permutations((1, 2, 3))
    )


def exact_check():
    upsets = [
        mask for mask in range(1, 1 << len(TRACES))
        if all(not (mask & (1 << i)) or (mask & up) == up
               for i, up in enumerate(UPSETS_CONTAINING))
    ]
    assert len(upsets) == 148
    eligible = after_upsets = after_safe = 0
    survivors = []
    for mask in range(1, 1 << len(TRACES)):
        if (mask & TOP_MASK) != TOP_MASK:
            continue
        family = [t for i, t in enumerate(TRACES) if mask & (1 << i)]
        if any(not (mask & (1 << INDEX[t | u]))
               for t, u in combinations(family, 2)):
            continue
        eligible += 1
        if any(is_useful_addition(up & ~mask) for up in upsets):
            continue
        after_upsets += 1
        # Union with existing full-leaf sets must stay in that family.
        safe = {u for u in TRACES if all(mask & (1 << INDEX[t | u]) for t in family)}
        if safe.isdisjoint(X_ONE_HIGH):
            continue
        after_safe += 1
        if not frequency_obstruction(safe):
            survivors.append(family)
    orbits = sorted({canonical_family(family) for family in survivors})
    result = eligible, after_upsets, after_safe, len(survivors), len(orbits)
    assert result == (2214, 567, 283, 28, 9), result
    return result, orbits


if __name__ == "__main__":
    (total, after_upsets, after_safe, after_weighted, orbit_count), orbits = exact_check()
    print(f"{total} eligible full-leaf trace patterns")
    print(f"{after_upsets} survive weak-counterexample enlargement")
    print(f"{after_safe} also admit a safe x-and-one-high trace")
    print(f"{after_weighted} survive the weighted frequency obstruction; "
          f"{orbit_count} up to relabeling the three high isolates")
    print("Canonical full-leaf trace profiles, bitmask in x,y,z,w order:")
    for orbit in orbits:
        print(" ".join(map(str, orbit)))

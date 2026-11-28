#!/usr/bin/env python3
"""Measure exact rank-filter strength at simple chamber roots for x9 < 150.

We relax 149 <= x9 < 150 to a closed interval. Beyond the interval, the
basic root uses singleton spacing; the stronger root adds two cuts.
This is a root candidate count, not a complete chamber search.
"""
from functools import lru_cache

CUTS = (158, 159, 161, 162, 168, 169, 171, 172)
BASE = tuple(tuple((mask >> i) & 1 for i in range(8)) for mask in range(256))


def interval(signs, strengthened):
    """Min/max of signs.dot(x) on the relaxed root, exactly as integers."""
    suffix = [0] * 10
    for i in reversed(range(9)):
        suffix[i] = signs[i] + suffix[i + 1]
    constant = sum((i + 1) * s for i, s in enumerate(signs))
    # x_i = i + accumulated nonnegative gaps, with x_0 = 0, weights 1-indexed.
    # Spare budget at gap index 10 has coefficient zero.
    budgets = ((38, 6), (39, 7), (63, 9), (1, 10)) if strengthened else ((140, 9), (1, 10))
    low = constant + sum(n * min(suffix[:k]) for n, k in budgets)
    high = constant + sum(n * max(suffix[:k]) for n, k in budgets)
    return low, high


@lru_cache(maxsize=None)
def possible_less(signs, strengthened):
    """Bounds (must be negative, may be negative) in a separated chamber."""
    if not any(signs):
        return 0, 0
    low, high = interval(signs, strengthened)
    assert low <= -1 or high >= 1
    return int(high < 1), int(low <= -1)


def intervals(a, strengthened):
    # Both lower-rank tests; and length from their difference:
    # Rank length = #`d<+M` - #`d<-M`, counting d=0 once.
    # For each B, use both sign bounds with d=B-A. The two lower-rank
    # contributions are d<0 and d<-M.
    rlo = rhi = 1
    llo = lhi = 0
    for b in BASE:
        d = tuple(y - x for x, y in zip(a, b))
        below = possible_less(d + (0,), strengthened)
        below_minus = possible_less(d + (1,), strengthened)
        below_plus = possible_less(d + (-1,), strengthened)
        rlo += below[0] + below_minus[0]
        rhi += below[1] + below_minus[1]
        llo += int(below_plus[0] and not below_minus[1])
        lhi += int(below_plus[1] and not below_minus[0])
    return rlo, rhi, llo, lhi


def counts(strengthened):
    profiles = [intervals(a, strengthened) for a in BASE]
    return tuple(sum(rlo <= k <= rhi and llo <= 148 <= lhi
                     for rlo, rhi, llo, lhi in profiles) for k in CUTS)


def main():
    # Simple scalar bounds check the indexing and budgets.
    for i, bounds in {5: (44, 147), 6: (84, 148), 8: (149, 150)}.items():
        assert interval(tuple(int(j == i) for j in range(9)), True) == bounds
    basic, stronger = counts(False), counts(True)
    assert all(b <= a for a, b in zip(basic, stronger))
    print("Representative rank: ", CUTS)
    print("Singleton gaps only: ", basic)
    print("With x6 and x7 cuts: ", stronger)


if __name__ == "__main__":
    main()

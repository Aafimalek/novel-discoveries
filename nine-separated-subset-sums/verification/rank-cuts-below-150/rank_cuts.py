#!/usr/bin/env python3
"""Exact finite check for the nine-cube cut table; no third-party packages."""
from itertools import combinations

N = 9
ORDER = [
    sum(1 << i for i in subset)
    for size in range(N + 1)
    for subset in combinations(range(N), size)
]


def boundary_size(k):
    initial = set(ORDER[:k])
    return len({v ^ (1 << i) for v in initial for i in range(N)} - initial)


def forbidden(start, length):
    left = min(start, (1 << N) + 1 - length - start)
    return 257 - length <= left <= (504 - length) // 2


def main():
    assert len(set(ORDER)) == 512
    profile = [boundary_size(k) for k in range(513)]
    assert max(profile) == 148
    cuts = [k for k in range(1, 512) if profile[k] == 148]
    assert cuts == [158, 159, 161, 162, 168, 169, 171, 172,
                    193, 194, 196, 197, 203, 204, 206, 207]
    assert [k for k in range(1, 513 - 149) if forbidden(k, 149)] == (
        list(range(108, 178)) + list(range(187, 257))
    )
    representatives = []
    for k in cuts:
        assert forbidden(k, 149) and forbidden(k - 1, 149)
        reflected = 513 - 148 - k
        assert reflected in cuts
        normalized = min(k, reflected)
        assert 257 - 148 <= normalized <= 177
        if k == normalized:
            representatives.append(k)
    assert representatives == cuts[:8]
    print("max boundary:", max(profile))
    print("tight cuts:", cuts)
    print("required edge representatives:", [(k, k + 148) for k in representatives])


if __name__ == "__main__":
    main()

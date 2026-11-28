#!/usr/bin/env python3
"""Exact small-dimensional replay; the all-n result uses the binomial proof."""
from itertools import combinations
from math import comb


def subset_sums(weights):
    sums = [0]
    for w in weights:
        sums += [w + x for x in sums]
    return sums


def verify(n):
    N = 1 << n
    m = n // 2
    H = sum(comb(j, j // 2) for j in range(n))
    W = sum(comb(2*j - 1, j - 1) for j in range(1, m + 1))
    S = 1 + sum(comb(2*j + 1, j) - comb(2*j + 1, j - 1)
                for j in range(1, m))
    order = [sum(1 << (i - 1) for i in a)
             for r in range(n + 1)
             for a in combinations(range(1, n + 1), r)]
    A = sum(1 << (i - 1) for i in range(1 if n % 2 else 2, n, 2))
    k = order.index(A) + 1
    kp = order.index(A | (1 << (n - 1))) + 1
    initial = set(order[:k])
    outside = {x ^ (1 << bit) for x in initial for bit in range(n)} - initial
    assert outside == set(order[k:kp])
    q = k + H - N // 2
    L = N + 1 - 2*k
    assert kp == k + H and comb(n, (n - 1)//2) + S == H
    assert L == H + W
    assert L >= (n - 1 if n == 3 else H + n - 1)
    assert 2*k <= N + 1 <= 2*(k + H) and 2*k + H <= N + 1
    assert q == 1 + W - (comb(2*m-1, m-1) if n % 2 == 0 else 0)
    return H, k, L


if __name__ == '__main__':
    for n in range(3, 15):
        H, k, L = verify(n)
        print(f'n={n:2}  H={H:5}  k={k:5}  central span={L:5}')
    x = [148, 225, 265, 285, 296, 302, 305, 307, 308, 309]
    assert len(set(subset_sums(x))) == 1024
    print('Checked the ten-weight integer witness at 309 (upper bound only).')
    assert verify(9) == (148, 158, 197)
    assert verify(10) == (274, 288, 449)
    assert verify(11) == (526, 674, 701)

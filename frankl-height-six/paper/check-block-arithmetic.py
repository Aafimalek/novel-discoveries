"""Check the finite arithmetic in the written k >= 14 argument."""
from math import comb
from fractions import Fraction

def H(m):
    return 1 + m + comb(m, 2)

def ceildiv(a, b):
    return (a + b - 1) // b

def max_initial_block(k):
    return max(r for r in range(2, k + 1) if H(k + 1 - r) >= 3*k)

assert [max_initial_block(k) for k in range(9, 14)] == [3, 3, 4, 5, 5]

for k, r, d, expected in [(9, 3, 2, 5), (10, 3, 3, 8), (11, 4, 2, 5), (12, 5, 1, 2)]:
    assert (r-1)*(d-1) < k-3-2*(r-2)
    assert ceildiv((k-2)*d, r) == expected
    assert 3*k+expected > H(k+1-r)

# All-pair case.
for k in range(9, 14):
    assert 3*k+comb(k-2, 2) > H(k-1)

# Extremal component-size partitions, with optional max degree.
def partitions(n, parts, minimum=1):
    if parts == 0:
        if n == 0:
            yield ()
        return
    for s in range(minimum, n//parts+1):
        for suffix in partitions(n-s, parts-1, s):
            yield (s,) + suffix

def max_edges(n, degree=None):
    def bound(s):
        return comb(s, 2) if degree is None else min(comb(s,2), degree*s//2)
    return max(sum(map(bound, sizes)) for c in range(5,n+1) for sizes in partitions(n,c))

assert [max_edges(n) for n in (8, 9)] == [6, 10]
assert [max_edges(n,3) for n in (8, 9, 10)] == [6, 7, 9]

for k, size in [(12,4),(13,5),(13,4)]:
    h = k-size
    e = max_edges(h)
    # Sum over the size-2 smallest edge counts, so at most this fraction of E.
    s = (size-2)*e//size
    W = (size-2)*h-s+ceildiv(comb(h,2)-e, comb(size,2))
    assert W > H(k+1-size)-3*k

for k, t_expected, e_expected in [(11,16,11),(12,17,10),(13,18,10)]:
    U = H(k-2)-3*k
    requirement = Fraction(comb(k-2,2)-U, 1) / (2-Fraction(6,k))
    t = ceildiv(requirement.numerator, requirement.denominator)
    assert t == t_expected
    E = ceildiv(9*t,k)-3
    assert E == e_expected and E > max_edges(k-3,3)
    assert 2**5 < 3*k

print("Verified all finite bounds for k=9,…,13 using exact integer and rational arithmetic.")

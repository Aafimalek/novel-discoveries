"""Independent check of f385 statistics, written separately from the C program.

For each listed n, compute G(n) = max{m + p(m) - n : m < n composite} straight from
the definition. Only m >= n - sqrt(n) - 1 can give a value >= 0, and every
reported value is >= 0, so the window is exact. Least prime factors come from
trial division by a precomputed prime list.

Usage: python verify_stats.py n1:g1 n2:g2 ...   (g = value reported by f385)
"""
import math
import sys


def primes_upto(limit):
    sieve = bytearray([1]) * (limit + 1)
    sieve[0:2] = b"\x00\x00"
    for i in range(2, int(limit**0.5) + 1):
        if sieve[i]:
            sieve[i * i :: i] = bytearray(len(sieve[i * i :: i]))
    return [i for i in range(limit + 1) if sieve[i]]


def least_prime_factor(m, primes):
    for p in primes:
        if p * p > m:
            return m
        if m % p == 0:
            return p
    return m


def G(n, primes):
    best = None
    s = math.isqrt(n) + 1
    for m in range(max(4, n - s - 1), n):
        p = least_prime_factor(m, primes)
        if p != m:
            value = m + p - n
            best = value if best is None else max(best, value)
    return best


pairs = [tuple(map(int, arg.split(":"))) for arg in sys.argv[1:]]
primes = primes_upto(math.isqrt(max(n for n, _ in pairs)) + 2)
bad = 0
for n, reported in pairs:
    value = G(n, primes)
    status = "ok" if value == reported else "MISMATCH"
    bad += status != "ok"
    print(f"n={n} G={value} reported={reported} {status}")
print("all match" if not bad else f"{bad} mismatches")

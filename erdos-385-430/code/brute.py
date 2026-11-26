"""Brute-force F(n) and the Erdos #430 term set straight from their definitions."""
import sys


def least_prime_factors(limit):
    spf = list(range(limit + 1))
    for i in range(2, int(limit**0.5) + 1):
        if spf[i] == i:
            for j in range(i * i, limit + 1, i):
                if spf[j] == j:
                    spf[j] = i
    return spf


def main():
    limit = int(sys.argv[1])
    spf = least_prime_factors(limit)

    def prime_factors(m):
        out = set()
        while m > 1:
            out.add(spf[m])
            m //= spf[m]
        return out

    best = None  # F(n) as a running maximum over composite m < n
    bad_385, bad_430, g_values = [], [], {}
    for n in range(2, limit + 1):
        m = n - 1
        if m >= 4 and spf[m] != m:
            value = m + spf[m]
            best = value if best is None else max(best, value)
        if n >= 4:
            best_or_zero = 0 if best is None else best  # sSup of the empty set is 0
            g_values[n] = best_or_zero - n
            if best_or_zero <= n:
                bad_385.append(n)
        if n >= 3:
            # Erdos 430 terms: 1 < m < n with every prime factor > n - m.
            terms = [m for m in range(2, n) if all(p > n - m for p in prime_factors(m))]
            if all(spf[m] == m for m in terms):
                bad_430.append(n)
    print("bad385", bad_385)
    print("bad430", bad_430)
    print("agree", [n for n in bad_385] == [n for n in bad_430 if n >= 4])
    print("G sample", [(n, g_values[n]) for n in (10, 100, 1000, 5000, limit) if n <= limit])


main()

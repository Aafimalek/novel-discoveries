"""Compare the binomial formula with the divisor-chain recurrence exactly."""

import argparse
from functools import cache
from itertools import product
from math import comb, isqrt


def divisor_chain_counts(limit: int) -> list[list[int]]:
    """Return each C_n as a list indexed by chain length, for 1 <= n <= limit."""
    counts = [[1] for _ in range(limit + 1)]
    for divisor in range(1, limit // 2 + 1):
        # Contributions from all proper divisors of divisor have already arrived.
        source = counts[divisor]
        for multiple in range(2 * divisor, limit + 1, divisor):
            target = counts[multiple]
            missing = len(source) + 1 - len(target)
            if missing > 0:
                target.extend([0] * missing)

            # Prepending multiple to a chain starting at divisor adds one step.
            for length, count in enumerate(source, start=1):
                target[length] += count
    return counts


def smallest_prime_factors(limit: int) -> list[int]:
    """Return the least prime factor of every integer from 2 through limit."""
    factors = list(range(limit + 1))
    for prime in range(2, isqrt(limit) + 1):
        if factors[prime] == prime:
            # Every smaller composite multiple has a smaller prime factor.
            for multiple in range(prime * prime, limit + 1, prime):
                if factors[multiple] == multiple:
                    factors[multiple] = prime
    return factors


def prime_exponents(n: int, factors: list[int]) -> tuple[int, ...]:
    """Use the factor sieve to return n's exponents in increasing prime order."""
    exponents = []
    while n > 1:
        prime = factors[n]
        exponent = 0
        while factors[n] == prime:
            exponent += 1
            n //= prime
        exponents.append(exponent)
    return tuple(exponents)


@cache
def binomial_chain_counts(exponents: tuple[int, ...]) -> tuple[int, ...]:
    """Evaluate the finite binomial sum, returning its coefficients by length."""
    counts = [0] * (sum(exponents) + 1)
    for indices in product(*(range(exponent + 1) for exponent in exponents)):
        prefix = 0
        term = 1
        for exponent, index in zip(exponents, indices, strict=True):
            # The second binomial uses only indices from earlier primes.
            term *= comb(exponent, index) * comb(exponent + prefix, exponent)
            prefix += index
        counts[prefix] += term
    return tuple(counts)


def main() -> None:
    """Check all coefficients through the requested limit and report mismatches."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("limit", nargs="?", type=int, default=1_000_000)
    arguments = parser.parse_args()
    if arguments.limit < 1:
        parser.error("limit must be positive")

    recurrence = divisor_chain_counts(arguments.limit)
    factors = smallest_prime_factors(arguments.limit)
    coefficient_count = 0
    for n in range(1, arguments.limit + 1):
        expected = tuple(recurrence[n])
        formula = binomial_chain_counts(prime_exponents(n, factors))
        if formula != expected:
            raise SystemExit(f"Mismatch at {n}: formula {formula}, recurrence {expected}")
        coefficient_count += len(expected)

    print(f"Matched {coefficient_count:,} coefficients for 1 <= n <= {arguments.limit:,}")
    print(f"Distinct ordered exponent tuples: {binomial_chain_counts.cache_info().currsize:,}")


if __name__ == "__main__":
    main()

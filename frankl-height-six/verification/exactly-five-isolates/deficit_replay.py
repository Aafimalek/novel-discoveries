"""Exact integer endgame for the five-isolate high-deficit exclusion."""
from collections import defaultdict
from math import comb


def partitions(total, minimum=1):
    if total == 0:
        yield ()
        return
    for first in range(minimum, total + 1):
        for tail in partitions(total - first, first):
            yield (first,) + tail


def charges_bound(d, partition):
    sizes = [e + 1 for e in partition]
    return (d - 1) * (1 + sum(sizes)) + sum(
        a * b - max(a, b)
        for i, a in enumerate(sizes)
        for b in sizes[i + 1 :]
    )


def check():
    expected = {3: (20, 10), 4: (39, 12), 5: (64, 14)}
    counts = defaultdict(list)
    for d, (expected_C, expected_limit) in expected.items():
        classes = list(partitions(d))
        C = max(charges_bound(d, p) for p in classes)
        assert C == expected_C
        # Tightened slack after one merger and at least one extra
        # unit of q deficit, multiplied by six.
        linear_coeff = 16 - 6 * d
        constant = 3 * (d * d - 9 * d) + 4 * C - 24 + 6 * d
        assert linear_coeff < 0
        limit = constant // (-linear_coeff)
        assert limit == expected_limit, (d, C, limit)
        for k in range(d + 2, limit + 1):
            for part in classes:
                nonsingletons = [e + 1 for e in part]
                n_singletons = k - 1 - sum(nonsingletons)
                if n_singletons < 0:
                    continue
                sizes = nonsingletons + [1] * n_singletons
                if len(sizes) < 3:
                    continue  # off-anchor triple needs three different groups
                max_off_degree_sum = 0
                for i, size in enumerate(sizes):
                    other_sizes = sorted(sizes[:i] + sizes[i + 1 :], reverse=True)
                    max_off_degree_sum += size * min(d - (size - 1), other_sizes[1])
                max_off_triples = max_off_degree_sum // 3
                through_anchor_loss = sum(comb(e + 2, 2) - 1 for e in part)
                max_loss = through_anchor_loss + 2 * max_off_triples
                needed_loss = (d - 2) * k + (6 + 7 * d - d * d) // 2 + 1
                assert max_loss < needed_loss, (d, k, part, max_loss, needed_loss)
                counts[d].append(max_loss - needed_loss)
    assert [len(counts[d]) for d in (3, 4, 5)] == [12, 24, 39]
    return expected, counts


if __name__ == "__main__":
    expected, counts = check()
    for d, (C, kmax) in expected.items():
        gaps = counts[d]
        print(f"d={d}: C={C}, k<={kmax}, {len(gaps)} rows, "
              f"loss slack from {min(gaps)} to {max(gaps)}, no survivors")

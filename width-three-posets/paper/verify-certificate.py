"""Independent exact checker for the finite tables in the accompanying note."""
from itertools import combinations
from fractions import Fraction
import json
from pathlib import Path


def branch_orders():
    for locations in combinations(range(5), 2):
        short, long = iter("xX"), iter("yYZ")
        yield "b" + "".join(next(short) if i in locations else next(long) for i in range(5))


def insert_a(order, cut):
    return order[:cut] + "a" + order[cut:]


def before(order, uv):
    return order.index(uv[0]) < order.index(uv[1])


def fits(terms, order):
    return all(before(order, uv) for uv, coefficient in terms if coefficient)


def component_score(terms, order, k):
    return sum(
        coefficient
        for j in range(k + 1)
        for uv, coefficient in terms
        if before(insert_a(order, j), uv)
    )


orders = list(branch_orders())
possible = {insert_a(order, cut) for order in orders for cut in range(1, 7)}
rows = json.loads((Path(__file__).parent / "certificate-data.json").read_text())
assert len(orders) == 10 and len(set(orders)) == 10 and len(possible) == 60
assert len(rows) == 25
for terms, bound, intended in rows:
    base = sum(c for uv, c in terms if uv == "ba")
    other = sum(c for uv, c in terms if uv != "ba")
    assert other > 0 and all(isinstance(c, int) and c > 0 for _, c in terms)
    assert bound == 23 * base + 20 * other
    assert set(intended) <= possible
    for order in orders:
        for k in range(7):
            assert 30 * component_score(terms, order, k) <= bound * (k + 1)

for order in possible:
    assert any(
        fits(terms, order) and (order[1] == "a" or all(uv != "ba" for uv, _ in terms))
        for terms, _, _ in rows
    )

quarter_x = [("ba", 12), ("ax", 6), ("xy", 2), ("xY", 1)]
quarter_y = [("ba", 12), ("ay", 6), ("yx", 2), ("yX", 1)]
for order in orders:
    assert fits(quarter_x, insert_a(order, 1)) or fits(quarter_y, insert_a(order, 1))
    for k in range(7):
        if before(order, "xZ"):
            assert component_score(quarter_x, order, k) <= 15 * (k + 1)
        assert component_score(quarter_y, order, k) <= 15 * (k + 1)

target = "baxXyYZ"

def obstruction_counts(s, t):
    weights = [(insert_a("bxXyYZ", i), 5*s+(t if i <= 1 else 0)) for i in range(4)]
    weights += [(insert_a("byYZxX", i), 2*s) for i in range(5)]
    total = sum(w for _, w in weights)
    counts = tuple(sum(w for order, w in weights if before(order, uv)) for uv in combinations(target, 2))
    return total, counts

mass_left, left = obstruction_counts(1, 0)
mass_right, right = obstruction_counts(1, 9)
for lc, rc in zip(left, right):
    low, high = 3*lc - 2*mass_left, 3*rc - 2*mass_right
    assert low >= 0 and high >= 0 and low + high > 0

for s, t in ((2, 1), (100, 1), (10, 89)):
    weights = [(insert_a("bxXyYZ", i), 5*s+(t if i <= 1 else 0)) for i in range(4)]
    weights += [(insert_a("byYZxX", i), 2*s) for i in range(5)]
    total = sum(w for _, w in weights)
    assert total == 30*s+2*t
    counts = {uv: sum(w for order, w in weights if before(order, uv)) for uv in combinations(target, 2)}
    assert all(3*c > 2*total for c in counts.values())
    p = Fraction(sum(w for order, w in weights if before(order, "ab")), total)
    assert p == Fraction(7*s+t, 30*s+2*t)
print("Verified: 25 rows × 70 exact inequalities; all 60 majority orders; quarter rows and obstruction.")

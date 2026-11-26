"""Regenerate the Euler CNFs and independently check their DRAT certificates."""

import argparse
import gzip
import shutil
import subprocess
import tempfile
from itertools import combinations, product
from pathlib import Path

from pysat.card import CardEnc
from pysat.formula import CNF, IDPool


def build(
    order: int,
    size: int,
    minimum: int,
    triple: bool = False,
    at_most: bool = False,
    euler: str | None = None,
) -> CNF:
    """Build the exact CNF for one of the cases specified in the paper."""
    symbols = range(order)
    groups = range(4)
    coordinate_pairs = tuple(combinations(groups, 2))
    words = tuple(product(symbols, repeat=4))
    pool = IDPool()
    formula = CNF()
    # Word variables record placements, and pair variables record their projections.
    word_variables = {word: pool.id(("word", word)) for word in words}
    pair_variables = {
        (i, j, a, b): pool.id(("pair", i, j, a, b))
        for i, j in coordinate_pairs
        for a, b in product(symbols, repeat=2)
    }
    supports = {pair: [] for pair in pair_variables}
    for word, variable in word_variables.items():
        projections = [(i, j, word[i], word[j]) for i, j in coordinate_pairs]
        formula.append([pair_variables[pair] for pair in projections])
        for pair in projections:
            supports[pair].append(variable)
    if triple:
        # A projected triple must contain a used pair in its three coordinates.
        for i, j, k in combinations(groups, 3):
            for a, b, c in product(symbols, repeat=3):
                formula.append(
                    [
                        pair_variables[i, j, a, b],
                        pair_variables[i, k, a, c],
                        pair_variables[j, k, b, c],
                    ]
                )
    for pair, pair_variable in pair_variables.items():
        support = supports[pair]
        # Exactly one occupied word supports a used pair. A repeated pair violates orthogonality.
        formula.append([-pair_variable, *support])
        formula.extend([[-variable, pair_variable] for variable in support])
        formula.extend(CardEnc.atmost(support, bound=1, vpool=pool).clauses)
    # The number of used pairs in a fixed projection equals the number of words.
    cardinality = CardEnc.atmost if at_most else CardEnc.equals
    formula.extend(
        cardinality(
            list(pair_variables.values())[: order**2], bound=size, vpool=pool
        ).clauses
    )

    # Any minimum-frequency symbol can be relabeled as 0 in group 0. Its other
    # coordinates are distinct in its incident words, so all three can be aligned.
    for label in range(minimum if euler != "wedge" else 0):
        formula.append([word_variables[0, label, label, label]])

    degree = {}
    for group, value in product(groups, symbols):
        partner = 1 if group == 0 else 0
        neighbors = [
            pair_variables[group, partner, value, other]
            if group < partner
            else pair_variables[partner, group, other, value]
            for other in symbols
        ]
        thresholds = [
            pool.id(("degree_at_least", group, value, degree))
            for degree in range(order + 1)
        ]
        degree[group, value] = thresholds
        # The number of incident used pairs within any other group equals the degree.
        # Enumerating the small truth table gives exact unary thresholds and no arithmetic variables.
        for pattern in product((0, 1), repeat=order):
            blocking = [
                -neighbor if bit else neighbor
                for bit, neighbor in zip(pattern, neighbors)
            ]
            total = sum(pattern)
            if total < minimum or (group == 0 and value == 0 and total != minimum):
                formula.append(blocking)
                continue
            for count in range(minimum, order + 1):
                formula.append(
                    [
                        *blocking,
                        thresholds[count] if count <= total else -thresholds[count],
                    ]
                )
        for count in range(minimum):
            formula.append([thresholds[count]])

    # Any unused pair leaves a rectangle in the other two groups with both sides at
    # least order minus its two degrees. Maximality requires all rectangle pairs to be used.
    for (i, j, a, b), pair_variable in pair_variables.items():
        for da, db in product(range(minimum, order + 1), repeat=2):
            remainder = order - da - db
            if remainder > 0 and remainder**2 + (order - remainder) * minimum > size:
                formula.append(
                    [pair_variable, degree[i, a][da + 1], degree[j, b][db + 1]]
                )

    # The remaining labels in each suffix can be sorted by degree independently.
    # The labels used by the normalized words can be permuted jointly across groups 1–3.
    for group in groups:
        if euler == "wedge":
            if group == 3:
                continue
            suffix_start = 3
        else:
            suffix_start = 1 if group == 0 else minimum
        sortable_pairs = list(
            zip(range(suffix_start, order - 1), range(suffix_start + 1, order))
        )
        if group == 1 and euler != "wedge":
            sortable_pairs.extend(zip(range(minimum - 1), range(1, minimum)))
        for first, second in sortable_pairs:
            for count in range(minimum + 1, order + 1):
                formula.append(
                    [-degree[group, first][count], degree[group, second][count]]
                )
    if euler == "wedge":
        # Each coordinate has exactly two degree units above its baseline of two.
        for group in groups:
            excess = [degree[group, label][cut] for label in symbols for cut in (3, 4)]
            formula.extend(CardEnc.equals(excess, bound=2, vpool=pool).clauses)
            for label in symbols:
                formula.append([-degree[group, label][5]])
        for label in range(4):
            formula.append([-degree[3, label][3]])
        # Normalize the two low endpoints and their four incident words.
        for word in ((0, 1, 0, 0), (0, 2, 1, 1), (1, 0, 0, 2), (2, 0, 2, 3)):
            formula.append([word_variables[word]])
        formula.append([-pair_variables[0, 1, 0, 0]])
        formula.append([-degree[1, 0][3]])
        for high in (4, 5):
            formula.append([degree[3, high][3]])
            formula.append([-degree[3, high][4]])
            for candidate in (3, 4, 5):
                formula.append([pair_variables[2, 3, candidate, high]])
    elif euler == "no_low":
        # The low label (0,0) only sees the two high labels in coordinate 1.
        formula.append([degree[1, 0][3]])
        formula.append([degree[1, 1][3]])
        for i, j in coordinate_pairs:
            for k in groups:
                if k in (i, j):
                    continue
                for a, b, c in product(symbols, repeat=3):
                    left = (i, k, a, c) if i < k else (k, i, c, a)
                    right = (j, k, b, c) if j < k else (k, j, c, b)
                    # For this branch there is no unused low pair with a common neighbor.
                    formula.append(
                        [
                            degree[i, a][3],
                            degree[j, b][3],
                            pair_variables[i, j, a, b],
                            -pair_variables[left],
                            -pair_variables[right],
                        ]
                    )
    return formula


# Each tuple specifies the order, word limit, minimum frequency, and case.
CASES = {
    "q3-m1": (3, 8, 1, True, True, None),
    "q3-m2": (3, 8, 2, True, True, None),
    "q5-m2": (5, 16, 2, True, True, None),
    "q5-m3": (5, 16, 3, True, True, None),
    "n6-f14-no_low": (6, 14, 2, False, False, "no_low"),
    "n6-f14-wedge-fast": (6, 14, 2, False, False, "wedge"),
}


def verify_case(
    name: str, checker: str, directory: Path, lrat_dir: Path | None
) -> None:
    """Check one DRAT trace and optionally export the same CNF with an LRAT trace."""
    formula = build(*CASES[name])
    cnf = directory / f"{name}.cnf"
    proof = directory / f"{name}.drat"
    formula.to_file(str(cnf))
    archive = Path(__file__).parent / "certificates" / f"{name}.drat.gz"
    with gzip.open(archive, "rb") as source, proof.open("wb") as target:
        shutil.copyfileobj(source, target)
    command = [checker, str(cnf), str(proof), "-q"]
    if lrat_dir is not None:
        command.extend(["-L", str(lrat_dir / f"{name}.lrat")])
    result = subprocess.run(
        command,
        capture_output=True,
        text=True,
        check=False,
    )
    if result.returncode != 0 or "s VERIFIED" not in result.stdout.splitlines():
        raise SystemExit(f"{name} failed verification\n{result.stdout}{result.stderr}")
    if lrat_dir is not None:
        shutil.copyfile(cnf, lrat_dir / cnf.name)
    print(
        f"{name}: VERIFIED ({formula.nv:,} variables, {len(formula.clauses):,} clauses)",
        flush=True,
    )


def main() -> None:
    """Check every case by default, with an option to rerun a single certificate."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--checker", default="drat-trim", help="path to the DRAT-trim executable"
    )
    parser.add_argument("--case", choices=tuple(CASES))
    parser.add_argument("--lrat-dir", type=Path, help="export CNFs and LRAT traces")
    args = parser.parse_args()
    if args.lrat_dir is not None:
        args.lrat_dir.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="euler-36-") as directory:
        for name in (args.case,) if args.case else CASES:
            verify_case(name, args.checker, Path(directory), args.lrat_dir)


if __name__ == "__main__":
    main()

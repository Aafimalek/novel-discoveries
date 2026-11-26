"""Construct and verify the finite examples in the Latin-square gap note."""

from itertools import combinations, product
from typing import Literal

BlockOrder = Literal[3, 4, 5, 7]
Word = tuple[int, int, int, int]
PROJECTIONS = tuple(combinations(range(4), 2))


def orthogonal_pair(order: BlockOrder, offset: int) -> list[Word]:
    """Return a full pair with all four label sets in [offset, offset + order)."""
    words = []
    for row, column in product(range(order), repeat=2):
        if order == 4:
            # Bits encode a + b*t in F_2[t]/(t^2 + t + 1).
            shifted = column << 1
            scaled = shifted ^ 0b111 if shifted & 0b100 else shifted
            first = row ^ column
            second = row ^ scaled
        else:
            # Over each odd prime field, the two Latin squares use slopes 1 and 2.
            first = (row + column) % order
            second = (row + 2 * column) % order
        words.append((offset + row, offset + column, offset + first, offset + second))
    return words


def disjoint_union(blocks: tuple[BlockOrder, ...]) -> list[Word]:
    """Join full pairs on disjoint consecutive label sets in every coordinate."""
    words = []
    offset = 0
    for order in blocks:
        words.extend(orthogonal_pair(order, offset))
        offset += order
    return words


def verify_maximal_pair(words: list[Word], order: int) -> None:
    """Check all pair projections and reject any possible additional word."""
    used: set[tuple[int, int, int, int]] = set()
    for word in words:
        if any(not 0 <= label < order for label in word):
            raise ValueError(f"Label outside order {order}: {word}")
        for i, j in PROJECTIONS:
            pair = (i, j, word[i], word[j])
            if pair in used:
                raise ValueError(f"Repeated pair {pair} in order {order}")
            used.add(pair)

    # A word can be inserted exactly when all six of its pairs are unused.
    for word in product(range(order), repeat=4):
        if all((i, j, word[i], word[j]) not in used for i, j in PROJECTIONS):
            raise ValueError(f"Order {order} admits insertion of {word}")


def main() -> None:
    """Check the claimed cell counts and maximality for all examples in the note."""
    examples: tuple[tuple[tuple[BlockOrder, ...], int], ...] = (
        ((3, 3), 18),
        ((4, 4, 4), 48),
        ((3, 4, 5), 50),
        ((4, 7, 7), 114),
    )
    for blocks, expected_count in examples:
        order = sum(blocks)
        words = disjoint_union(blocks)
        if len(words) != expected_count:
            raise ValueError(f"Expected {expected_count} filled cells, found {len(words)}")
        verify_maximal_pair(words, order)
        print(f"n={order}, F={len(words)}, blocks={blocks}: all {order**4:,} words checked")


if __name__ == "__main__":
    main()

# Independent C++ integer exclusion

This exact search enumerates sorted positive choices with largest weight in a specified range up to 148. The bitset tracks attainable sums; a branch is cut if adding a weight creates a collision, if too few distinct weights remain, or if even the best possible remaining weights cannot supply total weight 511 or squared-weight sum 87381. Distinctness forces the former by packing and the latter by the signed-moment argument formalized in `IntegerMomentBridge.lean`.

From the repository root:

```sh
g++ -O3 -std=c++17 nine-separated-subset-sums/verification/exclusion.cpp -o /tmp/nine-exclusion
/tmp/nine-exclusion 148 148
# To run every maximum from 1 to 148 instead:
/tmp/nine-exclusion 1 148
```

The exact-max-148 cloud check finished with no witness and printed:

```text
Cleared through 148 nodes by remaining depth: 0 73510218 234264883 22769404 1072211 44983 1727 54 1 0
```

This is an independently runnable exhaustive computation. It is not an end-to-end Lean proof, and the exact real optimum is still between 149 and 161.

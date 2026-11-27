# Independent integer search (not a Lean certificate)

Compile with `g++ -O3 -std=c++17 integer_exclusion.cpp -o integer-exclusion`. Run with no arguments for all maxima from 1 through 148, or with an inclusive range of maxima, e.g. `./integer-exclusion 148 148`.

The descending search holds the exact bitset of subset sums of its chosen weights. A new weight preserves distinctness iff the bitset and its translate are disjoint. Choices are restricted to positive integers in descending order. The largest possible remaining entries give upper bounds on the final sum and the final sum of squares. Each can be pruned only when its upper bound falls short of a necessary lower bound:

- Nine distinct subset-sum weights give 512 distinct integer sums from zero to the total, requiring a total at least 511.
- For the sorted 512 sums, any two at ranks i < j are at least j−i apart. Thus their population variance is at least (512²−1)/12 by the pairwise squared-distance formula. Uniform random inclusion independently selects each weight with probability 1/2, giving variance one quarter the sum of squared weights. Hence that sum must be at least 87381.

This provides an independently reproducible computation, not a Lean validation of the integer exclusion. The main paper cites Borwein and Mossinghoff's stronger integer optimum of 161.

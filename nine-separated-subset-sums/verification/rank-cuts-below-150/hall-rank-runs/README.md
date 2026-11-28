# Consecutive rank-148 runs and the four-category Hall filter

Assume nine positive sorted real weights have unit-separated subset
sums and 149 ≤ M=x9 < 150. This is a necessary-condition calculation,
not a search or exclusion of that entire interval. The rank cuts and
the forbidden band used below are from the [preceding rank-cut
argument](../README.md).

## Full runs from the eighth weight

Put t=floor(x8). For each cut k in 158,159,161,162,168,169,171,172,
the previous argument gives all ranks k+1 through k+148 in the
external boundary of the first k ranks. Consider the upper endpoints
j from max(k+t+1,257) through k+148. Their neighbors among the first k
ranks have rank difference >t, hence differ in coordinate 9. An edge
of length 149 would start at j−149 in the forbidden band, so the lower
rank is at least j−148. The lower endpoints are strictly increasing
as j increases: their real scores are obtained by subtracting the
same M. The last lower endpoint is forced to have rank k, so each
earlier endpoint must have rank exactly j−148. This proves length-148
edges starting at every rank

    max(109,k+t−147), ..., k.

An interval with lower endpoint above k is empty. Rank complementation
gives the reflected runs. If t≤120, the union contains the 42
consecutive starts 131 through 172. Consecutive attained starts
imply consecutive base masks in the order of eight-weight scores:
a base mask ordered between them would give an intervening unshifted
rank. Along a run of r≤149, the endpoint score difference is at most
M−148+(r−1). In fact subtract the 148−(r−1) unit rank gaps between
the last start and the end of the first edge, which has score
length M. Each consecutive score gap in the run is thus between
1 and M−147.

## A Hall filter for a fixed start r and base mask

For each proposed mask A and each other base mask B, write
d=s(B)−s(A). The four categories are d<−M, −M<d<0, 0<d<M, M<d.
Their allowable choices are determined by the three signs of
d+M,d,d−M, with integer bounds from the closed root relaxation.
Any nonzero difference in the true problem has magnitude at least
one. If f is the first-category count and j is the second, the
proposed lower rank and length imply

    r = 1+2f+j,       148 = 1+j+third.

Thus the category capacities must be (f,r−1−2f,147−(r−1−2f),108−f).
For each candidate f with nonnegative capacities, count how many
other masks have all of their allowed categories inside each set
T of categories (16 choices). This must not exceed the sum of
capacities of T. These are precisely the capacitated Hall
inequalities for the categories: replace each category by its
capacity in slots and apply ordinary Hall to those items whose
allowed category union is inside T. The individual sign choices
are only interval bounds, not a single common realization.

The replay yields 75,76,78,76,79,77,78,79 candidate masks at the eight
original starts, both with and without the optional sixth- and
seventh-weight lower cuts. The older strengthened relaxation tested
rank and length separately and retained 122–124 per start.

For the closed relaxation x8≤121 (necessary for t≤120), the 42
rank layers have 71–76 candidates each. A simple pairwise necessary
adjacency test does not reduce these counts: it allows paths that
may fail common-weight consistency. Only the root Hall filter and
rank-run lemma, not a stronger search claim, are asserted.

Run with Python 3.10+, no solver or Lean:

    python3 hall_ranks.py

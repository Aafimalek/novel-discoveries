# A quarter bound for a fork into two two-element arms

Let (P) be a finite poset and let (a,b) be incomparable, with every strict predecessor of (a) a strict predecessor of (b). Suppose the exclusive upset
[
S={z:ble z, a
leq z}
]
is exactly the five distinct vertices (b,x,X,y,Y), with (b<x<X) and (b<y<Y). Extra cross-comparabilities between the two arms are allowed. If a uniformly random linear extension has (Pr(a<b)le 1/4), there is a balanced pair among (a,b,x,X,y,Y).

For each of the six shuffles (pi) of the two ordered arms after (b), let (q_pi(j)) count extensions with branch order (pi) and with precisely (j) branch vertices before (a), for (j=0,ldots,5). An incompatible shuffle just has zero counts. The branch-order-preserving swap sends any extension at cut (j+1) into an extension at cut (j) of the *same shuffle*, and is injective. Hence each (q_pi) is antitone. In any one shuffle, the local ranking of the six vertices is determined exactly by inserting (a) at cut (j). The integer pair count is therefore the sum of (q_pi(j)) over the corresponding order relation, and the total count is the sum over all cuts.

The Lean theorem `TwoArmsMix.balanced_quarter_bins` (in `TwoArmsBins.lean`) proves that six such antitone histograms admit a balanced comparison if four times the count for (a<b) is at most the total. Its proof takes differences (w_pi(k)=q_pi(k)-q_pi(k+1)), with the last outer count zero. Thus a unit of (w_pi(k)) supplies a unit at each cut from 0 through (k). For a given pair, let the component count be the number of those cuts with the prescribed order. A comparison count is the weighted sum of component counts and the global population is the weighted sum of (k+1). Without balance, the >2/3 comparisons are a transitive total order (an oriented 3-cycle contradicts the union bound). Enumerating the six shuffles, and the position of (a) among the four nonroot vertices, gives a finite list of weighted component inequalities checked by kernel reduction in `TwoArmsMix.lean`; each contradicts its putative majority orientation. The 1/4 threshold is for this exclusive-upset shape, not for arbitrary width-three posets.

## Sharpness of the histogram relaxation, not of the poset theorem

Use only the branch orders (pi_0=bxXyY) and (pi_5=byYxX). Give component weights
[
w_{pi_0}(1)=t,quad w_{pi_0}(3)=2s,quad w_{pi_5}(3)=s
]
for (0<t<3s), all others zero. The total is (2t+12s) and the count (a<b) is (t+3s). The resulting probability is strictly greater than 1/4 and tends to 1/4 as (t/s	o0). The most weakly supported among the comparisons (a<x,a<X,a<y,a<Y) and all forward cross-arm pairs is supported by (2t+8s> rac23(2t+12s)). Also (b<a) is supported by more than 2/3, as (t<3s). Thus there is no balanced pair in the histogram model. The particular weights (t=6,s=8) give 5/18, with non-balance checked in Lean. It is not a poset counterexample.

## Certificate table (one row per majority order, up to exchanging arms)

Each row means the linear form is at most A·N+B·#(a<b). Every comparison in the linear form must exceed 2N/3 under the indicated majority order. The bound is incompatible when p≤1/4. To check each row, evaluate it on the 36 cutoff components independently; multiply by the component weights and sum.

| Majority order | Linear form on pair counts | A | B |
|---|---|---:|---:|
| `baxXyY` | 2·#(a<x) + 1·#(X<y) | 1 | 4 |
| `bxaXyY` | 11·#(x<a) + 2·#(a<X) + 4·#(a<y) | 11 | 0 |
| `bxXayY` | 2·#(X<a) | 1 | 0 |
| `bxXyaY` | 6·#(X<a) + 3·#(y<a) | 4 | 0 |
| `bxXyYa` | 3·#(X<a) + 3·#(Y<a) | 2 | 0 |
| `baxyXY` | 6·#(a<x) + 2·#(x<y) + 1·#(X<Y) | 3 | 12 |
| `bxayXY` | 12·#(x<a) + 6·#(a<y) + 1·#(y<X) | 12 | 0 |
| `bxyaXY` | 6·#(y<a) + 1·#(x<y) | 4 | 0 |
| `bxyXaY` | 6·#(X<a) + 1·#(y<X) | 3 | 0 |
| `bxyXYa` | 3·#(X<a) + 3·#(Y<a) | 2 | 0 |
| `baxyYX` | 2·#(a<x) + 1·#(x<y) | 1 | 4 |
| `bxayYX` | 12·#(x<a) + 6·#(a<y) + 1·#(y<X) | 12 | 0 |
| `bxyaYX` | 6·#(y<a) + 1·#(x<y) | 4 | 0 |
| `bxyYaX` | 6·#(Y<a) + 1·#(x<y) | 3 | 0 |
| `bxyYXa` | 3·#(X<a) + 3·#(Y<a) | 2 | 0 |

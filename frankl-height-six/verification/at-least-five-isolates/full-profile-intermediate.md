# Supplement: the nine full-leaf profiles collapse to one

This written reduction is superseded for proving at least five
isolates by the one-set repair, which closes the residual without
using this profile calculation. It records the narrower exact
path requested before that proof was found.

Let B have 2a+1 members, x occur a+1 times, and the high isolates
i,j,k each occur at most a times. For each high k, the class X_k
of members with trace exactly {x,k} is nonempty. Otherwise weight
i,j, the other two highs, by one each and weight k by zero.
Each x-containing member scores at least one, since neither
{x} nor {x,k} occurs. Their full-trace top and L co-leaf
maxima each score two. Each x-free member scores at least one
unless its trace is empty or {k}, and the x-free high top scores
two. Thus the total score is at least

    (a+1)+(L+1)+a−Y_k−Y_0+1 = 2a+L+3−Y_k−Y_0,

where Y_k is the number of members with exact trace {k} and
Y_0 counts empty trace. Since the total is at most 2a, we need
Y_k+Y_0≥L+3. But Y_0≤1, because a two-chain of empty traces
would precede a maximal five-member chain in the source-containing
family. The exact singleton-{k} fiber is union-closed and has
height at most two (append the four source-containing members
from trace {k} to full trace). It has at most L+1 members:
remove the fixed isolate, take its union maximum, and observe
that distinct proper members union to that maximum, so their
nonempty relative complements are disjoint. Thus Y_k+Y_0≤L+2,
contradiction. The proof applies even if all three X classes
were absent: simply choose any k.

If the full-leaf trace family M contains ∅ or {k}, unioning
that full-leaf member with a member of X_k forces {x,k} into M.
Apply this implication to the prior exact log's nine canonical
rows (source bit convention x,y,z,w has masks 1,2,4,8):

| Row | Present trace used | Missing trace forced |
| --- | --- | --- |
| 2 | empty (0) | xw (9) |
| 3 | empty (0) | xz (5) |
| 4 | w (8) | xw (9) |
| 5 | w (8) | xw (9) |
| 6 | z (4) | xz (5) |
| 7 | y (2) | xy (3) |
| 8 | y (2) | xy (3) |
| 9 | y (2) | xy (3) |

The only survivor is row 1, which contains all 15 traces.
No enumeration beyond the existing nine-row canonical log
is used. The basic all-three-classes bound does not use the
one-set repair lemma.

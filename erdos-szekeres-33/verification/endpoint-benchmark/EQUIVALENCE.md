# Why the endpoint-chain and quadruple-parity relaxations agree

This is an abstract argument about strict order labels and Boolean
orientation signs, not a geometric realizability theorem. The local packet
lemmas are proved in `PacketDP.lean`. This full equivalence and the numbered
DIMACS generation have not been formalized.

For increasing labels `a < b < c < d`, write a packet as
`(χ(abc), χ(abd), χ(acd), χ(bcd))`. A legal packet changes sign at
most once. The six ternary constraints in the upstream generator are
equivalent to this condition (16 local patterns). Two consequences:

1. If a legal packet's first and last signs agree, all four signs agree.
2. If the middle two signs differ, the first equals the second and the
   fourth equals the third.

A monochromatic chain may initially mean that only its **consecutive**
triples have one color. In a signotope all its triples then have that color:
induct on its length, applying the hypothesis to the prefix and suffix.
The only remaining triples use both endpoints. For any such triple in
a chain of at least four labels, insert a second interior label to form a
packet. Its first and last signs are already fixed by the prefix and suffix,
so consequence 1 fixes the desired triple. Thus shortening a chain while
retaining its endpoints preserves its color.

A legal packet has even parity exactly when its first two signs agree and
its last two signs agree. Consequently a set (S) of at least four labels
whose packets all have even parity has a simple description. Write its
endpoints as (L,R), and assign each interior label (x) a color
`c(x) = χ(L,x,R)`. For each increasing triple (a<b<c) in (S),
its sign is (c(b)): if (a>L), the last pair of the packet (L,a,b,c)
allows replacing (a) by (L); if (c<R), the first pair of the packet
(L,b,c,R) allows replacing (c) by (R). Splitting the interiors by
(c(x)), and adjoining (L,R) to both classes, gives a cup and a cap,
of total length (|S|+2). One chain may consist of just the two endpoints.

Conversely, take two opposite-color chains with shared endpoints (L,R).
Their interiors cannot intersect: a common interior label would force
`χ(L,x,R)` to be both colors. For any two interior labels (a<b),
their chain colors determine
`χ(L,a,b) = c(a)` and `χ(a,b,R) = c(b)`.
If their colors agree, use monochromaticity of that chain; if they differ,
use consequence 2 on the packet (L,a,b,R). Now consider three interior
labels (a<b<c). If they share a color, their sign is that color. Otherwise
at least one of these alternatives applies:

- `c(a) ≠ c(b)`: in the packet (L,a,b,c), the first and third
  signs are (c(a),c(b)), respectively, so the fourth must equal the third.
- `c(b) ≠ c(c)`: in the packet (a,b,c,R), the second and third signs
  are (c(b),c(c)), respectively, so the first must equal the second.

Thus again every triple has the color of its middle point. Every
packet in the union has form `(c(b), c(b), c(c), c(c))`, hence even parity.
So the two descriptions of an abstract convex (k)-set agree under
the legal-packet rule.

The upstream dynamic program introduces pair-endpoint and triple-boundary
states for cup/cap lengths `2,…,k`. The exact intended interpretation
is *there exists a chain of this color/length with these endpoints or
specified boundary*. Units set length 2, orientation literals set length
3, and the ternary implications propagate actual chain extensions
(cap to the right, cup to the left). Projection and shortening clauses
then force endpoint states for all chains found in the sign assignment.
The CNF implications are only one-way; an arbitrary auxiliary model need
not denote exact chain existence. But (i) it cannot set false a state
forced by an actual chain, and (ii) setting exactly the actual chains
satisfies all the structural clauses. Therefore when the three parameters
are all (k), the forbidden pairs of endpoint states, with
(d+e=k+2), exclude exactly the same orientation assignments as the
quadruple-parity avoidance clauses. The standalone no-(k)-cup or
no-(k)-cap units agree with that exclusion, including when one chain
has length 2. Longer witnesses can be shortened to the threshold.

Every true real counterexample has legal packets and produces a
satisfying sign-and-state assignment, so an independently checked UNSAT
certificate for either encoding can rule out a real counterexample,
conditional on the appropriate geometry-to-numbering link. A SAT signotope
model is **not** by itself a real counterexample. Without the packet
constraints one cannot apply the preceding argument.

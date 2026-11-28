# A one-set repair excludes the remaining four-isolate case

**Written proof, not yet checked end to end in Lean.** A weak
ground-minimal counterexample at height at most six has at least five
isolated points. The [at-least-four bound](../at-least-four-isolates/) and
[exactly-four reductions](../exactly-four-isolates/) already exclude
every case except the single-source model in which its containing
fiber has the 15 possible isolate traces other than one distinguished
singleton. The following argument eliminates that last model.
It does not depend on the subsequent nine-profile calculation or
the example-specific toggle cuts.

## One-set repair lemma

Let G be a finite union-closed family of nonempty sets with no strict
seven-member chain. Suppose B is a nonempty union-closed subfamily
whose ground is strictly smaller than the ground of G, and that G
contains a member strictly above every member of B. Suppose that

- b=|B| is odd;
- a point x occurs in exactly (b+1)/2 members of B;
- every other point occurs in at most (b−1)/2 members of B; and
- B does not contain {x}.

Then there is a finite nonempty union-closed family H of nonempty
sets, on the ground of B, with no strict seven-member chain and no
point occurring in more than half of its members.

**Proof.** There exists A in B containing x but with
C=A without x not in B. If not, deleting x would inject the x-containing
members into the x-avoiding members, contradicting the frequencies.
Choose A inclusion-maximal among those with an absent deletion.
The proposed single added set C is nonempty, since B does not
contain {x}. Put H=B together with C.

If D in B contains x, then C union D is A union D and belongs
to B. If D avoids x, consider the member A union D of B.
If it equals A, then C union D=C; if it strictly contains A,
its x-deletion belongs to B by maximality. That deletion is exactly
C union D. This proves union closure of H. Its size is b+1.
The x-frequency remains (b+1)/2, and each other frequency is
at most (b−1)/2+1. Hence H has no strict majority.

For height, consider a strict chain in H using the new set C.
The chain prefix strictly below C consists of B-members not
containing x. Leave this prefix unchanged. Replace C and every
later set D by its union with A. The first replacement is A,
and each later replacement is D with x adjoined, since D
contains C. All the replacement sets belong to B by union
closure (and the first is A itself).

The replacement sequence is nested. Appending x can collapse
two distinct consecutive sets only when the lower one omits x
and the upper one contains x. Along any strict inclusion chain
there is at most one such transition, so the replacement loses
at most one strict step. The unchanged prefix remains strict
at the boundary: it omits x, and A contains x. If a strict step
was lost, append the member of G strictly above all of B.
We obtain a strict chain in G of the original length. A chain
in H not using C already belongs to G. Therefore H has no
strict seven-member chain. Finally, adding C does not enlarge
the ground of B. This proves the lemma.

## Application to four isolates

Use the weak convention: G is a finite nonempty union-closed family
of nonempty sets, every point occurs in at most half the members,
there is no strict seven-member chain, and its ground is minimum
among all families with those properties.

The previously established written bound gives at least four
isolates. At exactly four isolates, the preceding block-deficit
proof excludes two or more sources, and zero sources are impossible
by the published 12-point theorem (add the empty member to pass
from a weak counterexample to a strict below-half counterexample).
The exact trace classifier for the single source p leaves only
the containing fiber P with 15 traces, all except {x}, where x
is an isolate. Every P-set contains the full forcing star.
In P, x occurs seven times and each of the other three isolates
eight times; each leaf occurs in all 15 sets.

Let B be the family of members not containing p, of size b.
Its ground is smaller, it remains union-closed, and the original
union maximum U of G strictly contains every B-member (because
U contains p). The full-family frequency bounds imply

    2 f_B(x) ≤ b+1,
    2 f_B(y) ≤ b−1  for each other isolate y,
    2 f_B(l) ≤ b−15 for each leaf l.

The family B is nonempty: otherwise p is universal in G. By
ground minimality applied to B itself, some point occurs strictly
more than half in B. Only x can do so, and the first displayed
bound forces b odd and f_B(x)=(b+1)/2. B does not contain {x}
because weak counterexamples have no singleton (or because the
15-trace pattern forbids an isolate trace equal to {x}, by union
with the full star). Thus B meets every hypothesis of the
one-set repair lemma. It produces H on the smaller ground,
contradicting the minimum-ground assumption.

This excludes the last exactly-four case. Combining it with the
earlier exclusions proves that at least five isolates are
necessary, not the unrestricted height-six conjecture.

## Verification scope

The [paper PDF](at-least-five-isolates.pdf) incorporates the new repair
lemma and its [surplus-d generalization](multiple-repair.md). To replay
the inherited finite classification, run `python3 traces.py` and
compare against `traces.log`.

The new repair lemma is entirely handwritten. Its inputs are
the previously checked weak singleton exclusion / ground
minimality framework and the written four-isolate block proof
plus exact 105-of-106 trace replay. No 9-profile refinement,
external solver, or new Lean compilation is a dependency of the
repair lemma. The published 12-point result is used only in the
preceding multiple-source / zero-source reductions, as described
there.

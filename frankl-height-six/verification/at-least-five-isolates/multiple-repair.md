# A surplus-d version of maximal missing deletion

**Written lemma, not checked in Lean.** Let B be a nonempty
union-closed subfamily of a finite union-closed family G of
nonempty sets. Suppose a member of G strictly contains every
member of B, and G has no seven-member strict chain. Suppose
B does not contain the singleton {x}. Put b=|B| and let

    d = 2 f_B(x)−b > 0.

If every other point v satisfies 2 f_B(v)≤b−d, then there is a
union-closed family of nonempty sets with the same ground as B,
with no seven-member strict chain and with all frequencies at
most half. In particular this configuration is impossible if G
is weak ground-minimal and B has smaller ground.

Begin with B_0=B. At each stage t<d the number of members
containing x exceeds the number avoiding x: the former remains
f_B(x), and the latter has increased from b−f_B(x) by t.
Therefore in B_t there is some x-containing A with C=A without
x absent, since otherwise deletion would be an injection into
the x-avoiding members. Choose such A inclusion-maximal and
insert C. This is a nonempty set, and A is an original B member
since all insertions avoid x.

As in the one-set proof, if D∈B_t contains x then C union D
equals A union D and already belongs to B_t. If D avoids x,
then C union D is A union D with x deleted. It is C if A union D
equals A, and belongs to B_t otherwise, by maximality of A.
Thus every B_t is union-closed. No inserted set adds a point
to the ground. After d insertions the size is b+d; the
x-frequency is unchanged and exactly half the new size.
For every v≠x, the doubled frequency is at most b−d+2d=b+d.

Height is checked directly for B_d, not by increasing the
height loss one insertion at a time. Given a strict chain
using any inserted member, take its first inserted member C.
Write C=A without x with A∈B. Leave the prefix before C
unchanged. To each member of the suffix starting at C adjoin
x. Any original suffix member D extends C, so its lift is
A union D and belongs to B. Each inserted suffix member
lifts to its own original preimage in B by construction.
The suffix was nested, and adjoining the same x can identify
at most one strict step (the transition from x-absence to
x-presence). The boundary with the prefix is still strict.
If one step was lost, append the member of G strictly above
every member of B. This lifts a forbidden seven-chain in B_d
to G, contradiction. Chains with no inserted member are
already in G. This proves the lemma.

## One-source application

Let P denote the source-containing fiber of a proposed weak
ground-minimal counterexample, and B the smaller-ground
source-avoiding fiber. Suppose there is an isolate x with
f_P(x)<|P|/2 and every other active point v satisfies

    f_P(v) ≥ |P|−f_P(x).

The doubled excess of x in B is at most |P|−2f_P(x), since
G itself has the weak half bound. Every other point's
doubled deficit in B is at least
2f_P(v)−|P|≥|P|−2f_P(x). Since there is strict majority
in B by ground minimality, it can only be x. The lemma
applies: the full original union maximum contains the source
and is strictly above B, and singleton {x} is forbidden.
Thus this profile cannot occur, regardless of number of
isolates. For example, a full source-containing isolate cube
except for one singleton has this form at every size:
the other isolates are present exactly `2^(t−1)` times and x
`2^(t−1)−1` times.

There is a parity refinement when b and |P| have opposite
parity. Then the largest possible excess is
|P|−2f_P(x)−1, whereas the minimum deficit for v improves to
2f_P(v)−|P|+1. Hence the same conclusion needs only
f_P(v)≥|P|−f_P(x)−1 for every other active point, provided
|P|−2f_P(x)≥2. The refinement is conditional on b having that
opposite parity, not an unconditional elimination of those
trace families.

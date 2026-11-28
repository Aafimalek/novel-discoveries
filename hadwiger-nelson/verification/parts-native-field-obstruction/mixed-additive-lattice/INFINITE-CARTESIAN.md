# The whole additive α/β lattice is a Cartesian product

This handwritten theorem strengthens the finite pilot. It was
derived and audited without any further numerical search.

Let s=√−3, r=√33, and h=√−7, with imaginary square roots chosen
positive. Put ω=(1+s)/2, Λ=Z[ω], α=(r+s)/6, β=(3+h)/4.
Let

    M = Λ + αΛ + βΛ ⊂ C.

**Theorem.** The unit-distance graph on M is the exact Cartesian
product of three triangular lattice graphs. Its chromatic number
is exactly three. For any chosen distinct nonunit pair in M, a
proper four-coloring can give that selected pair the same color.
Consequently no two-terminal five-color forced-difference gadget
with nonunit terminal distance exists anywhere in M.

**Proof.** The square classes of -3,33,-7 are independent: the
exponents of 11 and 7 detect the second and third classes,
and -3 is not a rational square. Therefore 1,r,h,rh form a
basis of Q(s,r,h) over Q(s). Each displacement d has a unique
representation d=t+αu+βv with t,u,v∈Λ. In fact, writing

    d=A+rB+hC,
    A=t+3v/4+su/6,  B=u/6,  C=v/4,

the independence of 1,r,h shows immediately that the only zero
representation has t=u=v=0. The coordinates A,B,C lie in Q(s).

Let N(y)=y·conjugate(y). Ordinary complex conjugation fixes r
and negates h and s. Expand:

    N(d) =
      N(A)+33N(B)+7N(C)
      + r(A·conj(B)+B·conj(A))
      + h(C·conj(A)−A·conj(C))
      + rh(C·conj(B)−B·conj(C)).

The coefficient of r here lies in Q; the indicated coefficients
of h and rh are purely imaginary in Q(s), hence rational
multiples of s. Since the independent real directions are
1,r,hs,rhs, rational N(d) forces all three cross terms to
vanish separately. Equivalently A is perpendicular to B and
C is parallel to each of A and B, wherever the vectors are
nonzero. We now assume N(d)=1.

* If B,C are both nonzero, the conditions force A=0.
  Multiplying the equation A=0 by 12 gives
  12t+9v+2su=0 in Λ; reduction mod 2Λ implies v∈2Λ.
  Therefore N(v)≥4 and already 7N(C)=7N(v)/16≥7/4>1,
  contradiction.
* If B≠0 and C=0, then 33N(u)/36≤1 forces N(u)=1
  because a nonzero element of Λ has positive integer norm.
  Here A perpendicular to B makes t·conj(u) purely imaginary.
  Any purely imaginary element of Λ is an integer multiple of
  s: writing a+bω, its real part vanishes exactly if 2a+b=0.
  Thus t·conj(u)=ks for k∈Z. As N(u)=1, the equation
  N(A)=1−33/36 equals 3(k+1/6)^2=1/12. Only k=0 is
  integral, so t=0. This is a unit step in the α factor alone.
* If B=0 and C≠0, then 7N(v)/16≤1 forces N(v)=1 or 2.
  The norm N(a+bω)=a²+ab+b² is congruent to (a−b)²
  mod 3, ruling out 2. With N(v)=1, the parallel condition
  gives t·conj(v)∈Λ∩R=Z; write it as k. Hence
  N(A)=1−7/16 gives (k+3/4)^2=9/16. Only k=0 is
  integral, so t=0. This is a unit step in the β factor alone.
* If B=C=0, then d=t is a unit step in the first factor alone.

Conversely each of the three types of one-factor unit step is
an exact unit displacement because |α|=|β|=1. Thus the map
(t,u,v)↦t+αu+βv is a graph isomorphism from the Cartesian
product of the three triangular lattices onto the graph in
question.

In lattice coordinates (a,b), use color a+2b mod 3 and
sum three such colors modulo 3. Every unit displacement
changes one factor by one of ±(1,0), ±(0,1), ±(−1,1);
each alters its color by a nonzero residue. A triangle
within one factor attains the lower bound. For a chosen
distinct nonunit pair, both endpoints can be changed to
the same fresh fourth color: there is no edge between them
and every other site keeps one of the original three
colors. This proves the last assertion individually for
any pair; it does not assert one common coloring making
all nonunit terminal pairs equal simultaneously. ∎

## Scope

Enlarging the pilot by deeper additive sums of the same three
lattice factors cannot produce a six-chromatic unit-distance
obstruction or force a marked nonunit pair apart in five colors.
A coordinate search using these rotations must leave M.
For instance introducing a product rotation αβ allows a new
rh-component (αβ has nonzero coefficient of rh), and so is
not merely an additive enlargement of M. Whether that or
any similar family produces a useful gadget is not established.

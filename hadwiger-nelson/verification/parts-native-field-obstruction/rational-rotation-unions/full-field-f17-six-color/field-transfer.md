# A six-color upper bound for the complex rotation field

Let L = Q(√−3, √33, √−7), viewed as a subset of the complex plane
with usual distance. The unit-distance graph induced by L is
six-colorable. This is an upper bound for this field, not a claim
that all six colors are necessary or a bound for the full plane.

Let F = Q(√33, √21) be the real subfield of L, so
L = F(√−3), and write z = A + B√−3 with A, B in F. Complex
conjugation fixes F and sends √−3 to its negative. Hence the
ordinary squared distance for displacement z is A² + 3B² in F.

The radicands 33 and 21 have simple roots 4 and 2 modulo 17,
respectively. Hensel lifting gives an embedding of F into Q₁₇.
Let v be the restriction of the normalized 17-adic valuation
and O = {A in F : v(A) ≥ 0}. Its residue field is F₁₇:
it is a subfield of the residue field of Q₁₇ and contains the
prime field via reduction of the integers. Since −3 is
not a square in F₁₇, the quadratic form a² + 3b² is
anisotropic there. If one coefficient of a nonzero displacement
is zero, or their valuations differ, the valuation of its norm
is twice the smaller coefficient valuation (using v(0)=∞).
If the two finite valuations coincide, divide both by their common
power of 17. At least one reduced coefficient is nonzero, so
anisotropy rules out extra cancellation. Thus a norm-one
displacement has both coordinates in O.

Every unit edge is contained in a single additive coset of O² in
F². Choose one representative per coset, subtract it, and reduce the
two coefficients modulo 17. The resulting residue difference still
satisfies a² + 3b² = 1. Any proper six-coloring of that finite norm
graph therefore pulls back to a proper coloring on L. The relevant
choice of coefficients is (A,B), not ordinary Cartesian
coordinates (A,√3B). The approach uses the valuation-coset
argument of [Madore, Proposition 3.2](https://arxiv.org/abs/1509.07023),
applied to the norm form with the anisotropy verified above.

The finite certificate and the written field transfer are distinct.
A Lean certificate for the finite norm graph alone does not
formalize the Hensel lift, valuation, or pullback argument.

# A four-colour obstruction for prime-to-seven cyclotomic catalogue searches

This is a lightweight, Init-only Lean 4.36.0 verification of the prime-to-seven modular argument in the order-42 cyclotomic coordinate field used in Heule and Przybocki's [G449](https://arxiv.org/abs/2611.28518). It does not improve the 6–7 bound for the Euclidean plane. No upstream data are involved.

## Statements

- Mod7Trace: work in Fin 7 with its modular operations. If a*b=1, the trace a+b is in {1,2,5,6}. The four classes {0,3}, {1,4}, {2,5}, {6} separate differences in this set.
- Residue7: the integer residue map preserves addition, subtraction and multiplication. The inverse and difference rules hold for prime-to-seven integer denominators.
- CoeffPoly: integer lists represent polynomials in increasing coefficient order. Every named coefficient-lift identity is an ordinary Lean proof; coeffEq ignores trailing zeros. A normWitness for numerator p and common denominator d is the coefficientwise equality of p(X)*p(X^41) - d*d to Phi42(X)*w.
- Mod7Witness: Phi42 evaluates to zero at 3 and 5 mod 7, and the 41st powers swap the two roots. If p/d and q/e are given with denominators prime to seven and a normWitness for the common-denominator difference, their colors localizedColour p d and localizedColour q e are distinct. The theorem localized_colour_separates_of_witness depends only on propext and Quot.sound.
- Mod7Factor: the coefficientwise mod-7 identity Phi42 = (1-X+X²)^6 is checked. The color is compatible with fraction equality witnessed by a multiple of Phi42. The whole witnessed graph is four-colourable by graph_colourable_of_prime_to_seven_norm_certificates.
- ResidueTorus and Mod7Witness: the finite graph on pairs (x,y) with norm-one difference (x-u)*(y-v)=1 is exactly four-colourable. The checked invertible basis ((3,5),(5,3)) sends the six triangular torus offsets to the norm-one offsets and reflects adjacency. A putative three-colouring forces period three in a length-seven row, which contradicts adjacent colours. This is sharpness only for the finite residue graph.

## Geometric scope

For actual complex points p(zeta)/d and q(zeta)/e, the remaining mathematical step is to supply the polynomial norm witness. The standard written argument uses that the minimal polynomial of a primitive 42nd root zeta is the monic integer polynomial Phi42. A unit edge makes N(zeta)*N(zeta^41) - (d*e)^2 vanish, with N=e*p-d*q, so monic polynomial division gives an integer multiple of Phi42. The implication from real unit edge to existence of that witness is **not formalized in this package**. Once the witness is supplied, the entire prime-to-seven obstruction and the finite sharpness result are checked. The result does not cover vertices whose intrinsic coefficient denominators involve seven, or the unrestricted plane.

Run ./build.sh with Lean 4.36.0. All compiled modules import only Init or earlier files in this package. The published logs give the axiom audits; no solver or native decision proof was used.

# A four-color obstruction for prime-to-seven cyclotomic directions

Aafi Khan Malek, independent researcher, Ahmedabad, India · [aafimalek2032@gmail.com](mailto:aafimalek2032@gmail.com)

This is a negative control for a restricted search. It does not give a coloring of the whole cyclotomic field or improve the Hadwiger–Nelson bounds. It applies to arbitrary numbers of vertices and unit directions, not just the published G449 directions.

## Four colors suffice for the localized directions

Let $\zeta=e^{2\pi i/42}$ and let $R=\mathbb Z_{(7)}[\zeta]$ consist of the cyclotomic numbers whose coefficients in the integral power basis can be written over a common denominator coprime to 7. If every edge of a unit-distance graph on points in $\mathbb C$ has displacement in $R$, the graph is four-colorable.

**Proof.** The polynomial $\Phi_{42}$ satisfies $\Phi_{42}(X)\Phi_6(X)=\Phi_6(X^7)$. Hence modulo 7 it becomes $(X^2-X+1)^6$. The two elements $3,5\in\mathbb F_7$ are roots and are inverses of one another. Therefore evaluation at each defines a ring map $\rho_3,\rho_5:R\to\mathbb F_7$: polynomial multiples of $\Phi_{42}$ vanish at both roots, and all allowed denominators reduce to invertible elements. Equivalently, use $\mathbb Z[\zeta]\cong\mathbb Z[X]/(\Phi_{42})$ and extend both maps to the localization. Complex conjugation sends $\zeta$ to $\zeta^{-1}$ and interchanges $\rho_3$ with $\rho_5$.

If $w$ is an allowed unit displacement, $w\overline w=1$, so the images are $a$ and $a^{-1}$ for some $a\ne0$. In order of $a=1,\ldots,6$, the possible trace values $a+a^{-1}$ are $2,6,1,6,1,5$. Color a point of $R$ according to the group containing $\rho_3(z)+\rho_5(z)$:
```text
{0,3}  {1,4}  {2,5}  {6}
```
A difference within a group is $0$ or $\pm3$, never one of the allowed differences $\pm1,\pm2$. The coloring therefore separates endpoints. For vertices outside $R$, translate each occupied additive coset to $R$ and use the same rule. Edges cannot run between different cosets. ∎

The condition includes nonintegral directions. For example $(-11+4\sqrt{-3})/13$ has unit norm and belongs to $R$, since $\sqrt{-3}=2\zeta^7-1$.

### The finite residue graph itself needs four colors

On $\mathbb F_7^2$, join two pairs if the product of the two coordinate differences is 1. Its six step vectors are $\pm u,\pm v,\pm(u+v)$ where $u=(3,5)$ and $v=(5,3)$. These form the triangular torus in the $u,v$ basis (the determinant is nonzero). The trace rule above gives four colors. If there were a three-coloring, the triangles on $x,x+u,x+u+v$ and on $x,x+v,x+u+v$ would force the same color at $x+u$ and $x+v$. Consequently a color only depends on the sum of the two basis coordinates. On $\mathbb Z/7\mathbb Z$ each three consecutive sums would need distinct colors, so the color sequence would have period 3. Since 3 generates this group, it would also be constant, a contradiction. This sharpness result concerns the residue graph only: it does not assert a four-chromatic Euclidean subgraph of $R$.

## Exact independent audit of G449

Input: [the authors' pinned G449 coordinates and sparse6 graph](https://github.com/bprzybocki/G449/tree/125bfda97ed1d336f84694de04dedcfb349c5164); geometry from [Heule and Przybocki](https://arxiv.org/abs/2611.28518). Run `python3 audit_layers.py PATH_TO_INPUTS`; the script checks both SHA-256 hashes, parses the two formats with no dependencies, and checks all direction norms with integer polynomial arithmetic.

* The declared denominator is 49; the least common coefficient denominator is 7. The sizes of the eight cosets modulo $\mathbb Z[\zeta]$ are 1, 49, 49, 56, 63, 70, 77, and 84.
* 1,092 edges are integral displacements, and 1,106 cross cosets with denominator 7. The unoriented directions divide 21 integral to 28 nonintegral. The 21 integral directions are precisely the powers of $\zeta$ up to sign.
* All seven non-singleton layers are exactly three-chromatic on their internal edges: each contains a triangle, and the explicit integer linear function in the script colors every internal edge. A related general three-color result for roots-of-unity directions appears in [Davidson's preprint](https://arxiv.org/abs/2610.09474). The modular four-color rule also passes every internal edge.
* Every pair of non-singleton layers has at least one cross edge. The singleton has an edge to just one layer. This quotient is not a lower bound on vertex chromatic number.

In fact the full graph restricted to integral displacements also has a three-coloring by the same linear functional. If an integral cyclotomic number has complex norm 1, then so do all its Galois conjugates: conjugation commutes with every Galois automorphism in the cyclotomic field. By Kronecker's theorem this algebraic integer is a root of unity. Its order divides 42, since adjoining it along with the existing 42nd roots would otherwise give a cyclotomic field of strictly larger degree. The script checks that the linear functional takes a nonzero value on each of the 42 root displacements. Translation handles arbitrary additive cosets, as in the four-color proof above.

There is a more specific local signature. For a nonintegral direction written as $p(\zeta)/7$ with $p$ of degree below 12, the polynomial $p\bmod 7$ has root multiplicities $(6,5)$ at $(3,5)$ for 21 unoriented directions, and $(5,6)$ for the other seven. This is checked by integer binomial expansion in the script. Equivalently, each such direction has normalized prime-ideal valuations $(1,-1)$ or $(-1,1)$ above seven. To see the negative valuation, the two primes are $(7,\zeta-3)$ and $(7,\zeta-5)$, both of ramification index 6 by cyclotomic factorization. At the root of multiplicity 5, write the numerator as an integer polynomial in $\zeta-r$. Its coefficients of degrees less than 5 are divisible by 7 and the degree-5 coefficient is a unit. Here $\zeta-r$ is a local uniformizer: the ideal generated by it and 7 has valuation 1, and 7 has valuation 6. The unique lowest valuation in the polynomial is therefore 5, so division by 7 gives $-1$. Conjugation exchanges the primes and $w\overline w=1$ makes the other valuation $+1$. Thus this five-chromatic construction already uses only the smallest possible nonzero pole order at these primes; a catalogue allowing those poles is not ruled out by the finite-field coloring.

### A complete direction catalogue for denominators that are powers of seven

Write $K=\mathbb Q(\zeta)$, and choose the audited first-order pole direction $u=p(\zeta)/7$ with negative valuation at $(7,\zeta-3)$. Its coefficient row appears in `audit-results.txt`. Every $w\in\mathbb Z[\zeta,1/7]$ with $w\overline w=1$ is uniquely of the form
$$
w=\zeta^k u^n,\qquad k\in\mathbb Z/42\mathbb Z,\quad n\in\mathbb Z.
$$
Indeed, the valuations of $w$ at the two primes over seven are opposites, and every other prime has nonnegative valuation by membership in the localized ring. Choose the integer $n$ so that $u^n$ has the same valuations over seven. Then $w/u^n$ is integral at every finite prime and has conjugate norm 1. It is a power of $\zeta$ by the integral argument above. Valuations determine $n$, then the root determines $k$.

For pole order at most $B$ the resulting catalogue has $21(2B+1)$ unoriented directions. The minimum common power-of-seven denominator of the direction with exponent $n$ is $7^{\lceil |n|/6\rceil}$ because seven has valuation 6 at each of the two primes. In particular there are **63** directions with at most first-order poles, and **273** with normalized coefficient denominator dividing seven. Both catalogues are included as TSV files, with one canonical sign per direction and exact integer coefficient rows. The 63-direction catalogue contains all G449 directions. Testing the larger catalogue against the existing 449 points finds **exactly the same 2,198 edges** as the published sparse6 graph. Since any difference of those points has denominator dividing seven, no unit edges were omitted on that vertex set. The published five-coloring still checks. To go beyond this graph with these directions one needs additional or different vertices.

```sh
python3 audit_layers.py PATH_TO_INPUTS --catalogue first-pole-directions.tsv
python3 audit_layers.py PATH_TO_INPUTS --pole-bound 6 --catalogue denominator-seven-directions.tsv
```

### Every single grid-point extension is still five-colorable

Any further point in $\frac17\mathbb Z[\zeta]$ that has a unit neighbor in G449 is among the **229,320** outside points reached by one step of the complete denominator-dividing-seven catalogue. Every other point is isolated from G449. Under the published five-coloring, all but **34** outside neighbors miss at least one color and so can individually be added with no recoloring. For the 34 exceptions, `extension-witnesses.json` gives exact, separately checked five-colorings of each single-vertex extension. It also gives a five-coloring of the **483-vertex, 2,395-edge** graph obtained by adjoining all 34 exceptions at once, with all exact unit edges between them included. This rules out finding six colors by adding one point in this grid to the 449 existing points. It does not rule out an extension by a point outside the grid or by arbitrarily many additional points.

After regenerating the denominator-seven catalogue above, verify without a solver:
```sh
python3 check_extensions.py PATH_TO_INPUTS denominator-seven-directions.tsv unused extension-witnesses.json --verify-only
```
To reproduce the witness search, replace `unused` with the path to CaDiCaL and omit `--verify-only`. The certificate checker uses only the input hashes, the exact catalogue and direct edge and color checks. These finite G449 audits and the pole classification have not been formalized in Lean.

### What Lean checks

The [Lean subpackage](lean) checks the finite norm-trace rules, the exact factorization modulo 7, color compatibility with fraction equality witnessed by a multiple of $\Phi_{42}$, and proper four-coloring for graphs whose coordinate pairs have polynomial norm witnesses. It proves that the finite residue graph is not three-colorable. The classical implication from an actual complex unit edge to the needed monic-polynomial quotient remains written mathematics, not a Lean theorem in this package. The sources rebuild using only Init on Lean 4.36.0.

The search implication is specific: no catalogue using only prime-to-seven denominators in this field can produce a five- or six-chromatic example. A catalogue that also uses denominators divisible by seven is not excluded. No claim of a literature-wide novelty check is made.

ChatGPT assisted with proof development and verification; Codex was not used.

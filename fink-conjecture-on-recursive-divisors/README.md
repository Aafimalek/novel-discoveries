# Fink's conjecture on recursive divisors

This folder has a proof of Conjecture 1 from T. M. A. Fink, *Number of ordered factorizations and recursive divisors* ([arXiv:2307.16691](https://arxiv.org/abs/2307.16691), 2023). The proof is formalized in Lean 4 with mathlib.

Fink checked the conjecture for every $n \le 10^5$. His paper's open questions list ends with "Can Conjecture 1 be proved?" This folder answers yes, for every positive integer $n > 1$.

## The statement

Write $n = p_1^{\alpha_1} \cdots p_\omega^{\alpha_\omega}$ with distinct primes $p_k$. Let $\kappa_0(n)$ be the number of recursive divisors, defined by $\kappa_0(1) = 1$ and

$$\kappa_0(n) = 1 + \sum_{d \mid n,\ d < n} \kappa_0(d).$$

Equivalently, $\kappa_0(n)$ counts strict divisor chains $n = d_0 > d_1 > \cdots > d_\ell$ with $d_j \mid d_{j-1}$, including the chain of length zero. Fink showed $\kappa_0(n) = 2K(n)$ for $n > 1$, where $K(n)$ counts ordered factorizations of $n$.

Conjecture 1 says

$$\kappa_0(n) = 2K(n) = 2^{\alpha_\omega} \sum_{i_1=0}^{\alpha_1} \cdots \sum_{i_{\omega-1}=0}^{\alpha_{\omega-1}} \prod_{k=1}^{\omega-1} \binom{\alpha_k}{i_k} \binom{\alpha_{k+1} + i_1 + \cdots + i_k}{\alpha_{k+1}}.$$

## What is proved

The proof gives a stronger identity. Let $C_n(u)$ be the polynomial whose coefficient of $u^\ell$ counts strict divisor chains from $n$ of length $\ell$. Then

$$C_n(u) = \sum_{i_1=0}^{\alpha_1} \cdots \sum_{i_\omega=0}^{\alpha_\omega} u^{i_1 + \cdots + i_\omega} \prod_{k=1}^{\omega} \binom{\alpha_k}{i_k} \binom{\alpha_k + i_1 + \cdots + i_{k-1}}{\alpha_k}.$$

Setting $u = 1$ and summing out $i_\omega$, which only appears in $\binom{\alpha_\omega}{i_\omega}$, gives Conjecture 1. For example, $C_{12}(u) = 1 + 5u + 7u^2 + 3u^3$, so $\kappa_0(12) = 16$.

The research note gives two proofs:

1. A counting proof. It groups the quotients $d_{j-1}/d_j$ by their least prime factor and counts each group with stars and bars.
2. A formal power series proof. It solves the divisor recurrence as a nested product, one prime at a time.

Every term in the new formula is a product of nonnegative binomials. Earlier closed forms for the same counts, including Fink's Theorem 2 and the formulas of Law, Lettington and Schmidt, use alternating sums.

## Files

| Path | Contents |
| --- | --- |
| [`paper/fink-conjecture.pdf`](paper/fink-conjecture.pdf) | Two-page research note with both proofs |
| [`paper/fink-conjecture.tex`](paper/fink-conjecture.tex) | LaTeX source of the note |
| [`lean/FinkConjecture.lean`](lean/FinkConjecture.lean) | Lean 4 formalization |
| [`verification/verify_divisor_chains.py`](verification/verify_divisor_chains.py) | Exact numerical check of the chain-length formula |

## Check it yourself

### Lean

The project pins Lean `v4.36.0` and mathlib `v4.36.0`. With [elan](https://github.com/leanprover/elan) installed:

```sh
cd lean
lake exe cache get
lake build
```

The build prints the axioms the main theorems depend on:

```text
'Fink.divisorChains_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'Fink.fink_conjecture_1' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are the three standard axioms of Lean's mathlib. The list has no `sorryAx`, so the file has no unproved steps.

The file contains these results:

- `divisorChains_identity` proves the chain-length identity for any weight `u` in any commutative ring and any finite list of distinct primes. Take `u = Polynomial.X` over `ℤ` to count chains by length.
- `fink_conjecture_1` proves the printed form of Conjecture 1, including the factor $2^{\alpha_\omega}$.
- An `example` computes $\kappa_0(12) = 16$ straight from the recurrence, to check the definitions.

`divisorChains u n` is defined by the recurrence over `Nat.properDivisors`. The theorems take `n` as a product of prime powers, given as a list of distinct primes and their exponents. Every positive integer has this form, but the file does not restate the theorems for a bare `n : ℕ`.

### Python

```sh
python verification/verify_divisor_chains.py 1000000
```

The script computes $C_n(u)$ from the recurrence and from the formula, using exact integers. For $1 \le n \le 1{,}000{,}000$ all 4,626,619 coefficients agree. It needs Python 3.10 or later and runs in about 15 seconds.

## Priority

I found no earlier proof in Fink's posted versions, in the papers I found that cite it, or in the OEIS entry for $K(n)$ ([A074206](https://oeis.org/A074206)). This is a search result, not a guarantee. If you know of an earlier proof, please open an issue and I will credit it here.

## How this was made

The proofs, the Lean formalization and the verification script were developed with AI assistance (OpenAI Codex and Anthropic Claude). The Lean build checks the main result independently of how it was produced.

## References

- T. M. A. Fink, *Number of ordered factorizations and recursive divisors*, [arXiv:2307.16691](https://arxiv.org/abs/2307.16691), 2023.
- A. D. Law, M. C. Lettington and K. M. Schmidt, *Multifactorisations and divisor functions*, Utilitas Mathematica 125 (2025), 43-60, [doi:10.61091/um125-03](https://doi.org/10.61091/um125-03).

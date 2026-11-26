# Erdős Problems #385 and #430

Let $p(m)$ be the least prime factor of $m$, and let

$$F(n) = \max_{m < n,\ m \text{ composite}} \bigl(m + p(m)\bigr).$$

Erdős, Eggleton and Selfridge asked:

1. Is $F(n) > n$ for all sufficiently large $n$?
2. Does $F(n) - n \to \infty$?
3. Is perhaps always $F(n) \ge n + (1 - o(1))\sqrt n$? (Trivially $F(n) < n + \sqrt n$.)

These questions are [Erdős Problem #385](https://www.erdosproblems.com/385). [Problem #430](https://www.erdosproblems.com/430) is equivalent to the first one. Terence Tao [explained](https://terrytao.wordpress.com/2024/08/19/erdos-problem-385-the-parity-problem-and-siegel-zeroes/) why question 1 seems to need a breakthrough on the parity problem.

**Status: not solved.** The questions remain open for every large $n$. This folder settles all three for almost every $n$.

## Results

| Result | How it is checked |
| --- | --- |
| Problem #430 is equivalent to #385(i). A witness criterion for $F(n) > n$. Every exception $n \ge 7$ is even, has $n - 1$ prime and has $F(n) = n$. | Lean 4 ([`lean/Erdos430.lean`](lean/Erdos430.lean)) |
| For every fixed $T$, the $n$ with $F(n) \le n + T$ have density zero. | Lean 4 ([`lean/Erdos430Density.lean`](lean/Erdos430Density.lean)) |
| If $T(X) = o(\log X)$, then $F(n) > n + T(X)$ for all but $o(X)$ integers $n < X$. | Lean 4, same file |
| **$F(n) = n + (1 - o(1))\sqrt n$ for almost all $n$.** For each $\varepsilon > 0$ the exceptions below $X$ number $O(X / (\log X)^A)$. | Written proof in the [note](paper/erdos-385-430.pdf). Lean 4 checks the deduction (density zero) from three classical inputs taken as hypotheses ([`lean/Erdos430Sqrt/`](lean/Erdos430Sqrt/), see below). |
| Heuristic: $\min_{X \le n < 2X} (F(n)-n)/\sqrt n = 1 - (\tfrac12 + o(1))(\log X)^{3/2} X^{-1/4}$ | Matches exact data. The empirical constant stays near $\tfrac12$. |
| Exact values of $F(n)$ for every $n$ below the bound stated in the note | Independent replication of earlier searches |

The Lean files prove everything from the definitions. Lean reports only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`). The one analytic input, $\pi(x) = o(x)$, comes from Chebyshev's bound in mathlib.

### The $\sqrt n$ theorem in Lean, conditionally

Mathlib does not yet contain three classical results that the $\sqrt n$ proof uses, so the Lean theorem `Erdos430Sqrt.sqrt_almost_all` takes them as hypotheses (stated in [`Hypotheses.lean`](lean/Erdos430Sqrt/Hypotheses.lean)):

1. `MeanValueHyp`, the mean value theorem for Dirichlet polynomials (Montgomery–Vaughan) in the weak form $\int_{-T}^{T}|\sum_{n\le N}b_n n^{-it}|^2\,dt \le (2T + CN)\sum|b_n|^2$.
2. `ThetaHyp`, the prime number theorem with error: $|\vartheta(x) - x| \le Cx/(\log x)^{10}$ for $x \ge 2$.
3. `PrimeSumHyp`, a bound $|\sum_{P_1 \le p \le P_2} p^{-1-it}| \le C(1/(|t|\log Y) + (\log Y)^{-5})$ for $\sqrt Y/4 \le P_1$, $P_2 \le 4\sqrt Y$, $1 \le |t| \le Y^2$. It follows from the Vinogradov–Korobov zero-free region (Lemma 8 of the note).

From these, Lean proves that for every $\varepsilon > 0$ the $n < X$ with $F(n) < n + (1-\varepsilon)\sqrt n$ number $o(X)$. `F_le_add_sqrt` proves $F(n) \le n + \sqrt n$ for every $n$ with no hypotheses. Everything between the inputs and the conclusion is checked: Plancherel for the smoothed counts, the factorization into Dirichlet polynomials, the dyadic mean-square bound, the long-average lower bound, the count of exceptions in a block and the covering argument. Lean reports only the standard axioms.

So the hypotheses are the only unchecked part. They are standard theorems, but they are not machine-checked here. The rate $O(X/(\log X)^A)$ is only in the written proof. Neither proof has been refereed.

## What was already known

- Every $n$ with $F(n) \le n$ is one more than a prime, so such $n$ have density zero. A commenter on Tao's post noted this.
- The exceptions are OEIS [A322293](https://oeis.org/A322293): 100 values, the largest 267680.
- Searches on the problem's forum found no further exceptions up to $10^{11}$ and $1.0011 \times 10^{12}$.
- Tao remarked that an almost-all version should be within reach. As far as we know, no proof had been written down.
- Gafni and Tao ([arXiv:2508.06463](https://arxiv.org/abs/2508.06463)) proved that almost every prime gap $(p_k, p_{k+1})$ contains an $m$ with $p(m) \ge p_{k+1} - p_k$. This is a related question of Erdős; it does not imply the results here.

## Files

| Path | Contents |
| --- | --- |
| [`paper/erdos-385-430.pdf`](paper/erdos-385-430.pdf) | Research note |
| [`lean/Erdos430.lean`](lean/Erdos430.lean) | Reductions |
| [`lean/Erdos430Density.lean`](lean/Erdos430Density.lean) | Variance bound, finite inequality and density theorems |
| [Aafimalek/erdos-385-almost-all](https://github.com/Aafimalek/erdos-385-almost-all) | The same Lean development in Lean's module format, with Challenge/Solution files for the Palomar registry |
| [`lean/Erdos430Sqrt/`](lean/Erdos430Sqrt/) | The $\sqrt n$ theorem from three stated hypotheses; the final theorem is in `Final.lean` |
| [`code/f385.c`](code/f385.c) | Exact computation of $F(n) - n$ with a parallel segmented sieve |
| [`code/brute.py`](code/brute.py) | Both definitions computed directly, for cross-checking |
| [`code/aggregate.py`](code/aggregate.py) | Merges the chunk outputs of `f385` |
| [`code/ci_check.sh`](code/ci_check.sh) | Recomputes the exceptions below $10^7$ and compares |
| [`data/`](data/) | Exceptions, per-range minima below $5 \times 10^{11}$ (`summary_below_5e11.json`), distribution of $F(n) - n$ below $10^9$ |

## Check it yourself

```sh
cd lean && lake exe cache get && lake build      # Lean proofs; prints the axioms used
bash code/ci_check.sh                            # exceptions below 10^7, brute-force cross-check
gcc -O3 -march=native -fopenmp -o f385 code/f385.c -lm
./f385 4 10000000001                             # every n below 10^10, about 2 minutes on 8 cores
```

## How this was made

This work was AI-assisted (OpenAI Codex and Anthropic Claude). The Lean kernel checks the reductions, the density theorems, and the deduction of the $\sqrt n$ theorem from the three hypotheses above. Nothing here has been refereed.

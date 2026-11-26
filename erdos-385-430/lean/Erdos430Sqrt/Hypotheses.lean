import Mathlib

/-!
# The three classical inputs, stated as hypotheses

The theorem `Erdos430Sqrt.sqrt_almost_all` assumes exactly these three statements. Each is a
classical theorem of analytic number theory (or a weak consequence of one) that is not yet
in mathlib. They are hypotheses of the theorem, not axioms: nothing else is assumed.

* `MeanValueHyp` is the mean value theorem for Dirichlet polynomials of Montgomery and
  Vaughan (J. London Math. Soc. (2) 8 (1974)), in the weak form
  `∫_{-T}^{T} |∑_{n ≤ N} b_n n^{-it}|² dt ≤ (2T + C N) ∑ |b_n|²`.
* `ThetaHyp` is the prime number theorem with a power-of-log error,
  `|θ(x) - x| ≤ C x / (log x)^10`, which follows from de la Vallée Poussin's error term.
* `PrimeSumHyp` is a bound for prime sums `∑_{P₁ ≤ p ≤ P₂} p^{-1-it}` with `P₁, P₂ ≍ √Y` and
  `1 ≤ |t| ≤ Y²`: `≪ 1/(|t| log Y) + (log Y)^{-5}`. It follows from the Vinogradov–Korobov
  zero-free region through the explicit formula (Lemma 8 of the accompanying note, which
  even gives `exp(-c (log Y)^{1/3} (log log Y)^{-1/3})` in place of `(log Y)^{-5}`).
-/

open Complex Finset

noncomputable section

namespace Erdos430Sqrt

/-- Montgomery–Vaughan mean value theorem, in a weak form. -/
def MeanValueHyp : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (b : ℕ → ℂ) (T : ℝ), 0 ≤ T →
    ∫ t in -T..T, ‖∑ n ∈ Icc 1 N, b n * Complex.exp (-(((t * Real.log n : ℝ) : ℂ) * I))‖ ^ 2 ≤
      (2 * T + C * N) * ∑ n ∈ Icc 1 N, ‖b n‖ ^ 2

/-- Prime number theorem with error `O(x / (log x)^10)`, for Chebyshev's `θ`. -/
def ThetaHyp : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 2 ≤ x → |Chebyshev.theta x - x| ≤ C * x / Real.log x ^ 10

/-- Prime sums near `√Y` on the line `Re s = 1` (a consequence of Vinogradov–Korobov). -/
def PrimeSumHyp : Prop :=
  ∃ C Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y → ∀ P₁ P₂ : ℝ, √Y / 4 ≤ P₁ → P₂ ≤ 4 * √Y →
    ∀ t : ℝ, 1 ≤ |t| → |t| ≤ Y ^ 2 →
      ‖∑ p ∈ (Icc ⌈P₁⌉₊ ⌊P₂⌋₊).filter Nat.Prime,
          (p : ℂ)⁻¹ * Complex.exp (-(((t * Real.log p : ℝ) : ℂ) * I))‖ ≤
        C * (1 / (|t| * Real.log Y) + 1 / Real.log Y ^ 5)

end Erdos430Sqrt

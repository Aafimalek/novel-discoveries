import NineSeparatedSubsetSums.CachedFourPointCoverage
open scoped BigOperators
namespace NineSeparatedSubsetSums

private theorem emptyAssemblyRange137 (a : ℕ) (low : 148 ≤ a)
    (high : a ≤ 147) : NoDescendingTail a := by omega

private theorem prependAssemblyRange137 (n : ℕ) (now : NoDescendingTail n)
    (rest : ∀ a : ℕ, n+1 ≤ a → a ≤ 147 → NoDescendingTail a)
    (a : ℕ) (low : n ≤ a) (high : a ≤ 147) : NoDescendingTail a := by
  by_cases e : a = n
  · subst a
    exact now
  · exact rest a (by omega) high

/-- Both arithmetic dispatch and the real bridge are elaborated before any of the
concrete certificates are imported. The first arguments are just propositions. -/
theorem genericAssembly137
    (through122 : ∀ a : ℕ, 114 ≤ a → a ≤ 122 → NoDescendingTail a)
    (s123 : NoDescendingTail 123)
    (s124 : NoDescendingTail 124)
    (s125 : NoDescendingTail 125)
    (s126 : NoDescendingTail 126)
    (s127 : NoDescendingTail 127)
    (s128 : NoDescendingTail 128)
    (s129 : NoDescendingTail 129)
    (s130 : NoDescendingTail 130)
    (s131 : NoDescendingTail 131)
    (s132 : NoDescendingTail 132)
    (s133 : NoDescendingTail 133)
    (s134 : NoDescendingTail 134)
    (s135 : NoDescendingTail 135)
    (s136 : NoDescendingTail 136)
    (s137 : NoDescendingTail 137)
    (remaining : ∀ a : ℕ, 138 ≤ a → a ≤ 147 → NoDescendingTail a)
    (w : Fin 9 → ℝ) (hpos : ∀ i, 0 < w i)
    (sep : ∀ A B : Finset (Fin 9), A ≠ B →
      1 ≤ |(∑ i ∈ A, w i) - (∑ i ∈ B, w i)|) :
    ∃ i, 149 ≤ w i := by
  apply separated_nine_at_least_149_of_remaining_tails _ w hpos sep
  intro a hlo hhi
  by_cases low : a ≤ 122
  · exact through122 a hlo low
  · exact (prependAssemblyRange137 123 s123 (
      prependAssemblyRange137 124 s124 (
      prependAssemblyRange137 125 s125 (
      prependAssemblyRange137 126 s126 (
      prependAssemblyRange137 127 s127 (
      prependAssemblyRange137 128 s128 (
      prependAssemblyRange137 129 s129 (
      prependAssemblyRange137 130 s130 (
      prependAssemblyRange137 131 s131 (
      prependAssemblyRange137 132 s132 (
      prependAssemblyRange137 133 s133 (
      prependAssemblyRange137 134 s134 (
      prependAssemblyRange137 135 s135 (
      prependAssemblyRange137 136 s136 (
      prependAssemblyRange137 137 s137 (
      remaining)))))))))))))))) a (by omega) hhi

#print axioms genericAssembly137
end NineSeparatedSubsetSums

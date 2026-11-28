import NineSeparatedSubsetSums.CachedFourPointCoverage
open scoped BigOperators
namespace NineSeparatedSubsetSums

private theorem emptyAssemblyRange147 (a : ℕ) (low : 148 ≤ a)
    (high : a ≤ 147) : NoDescendingTail a := by omega

private theorem prependAssemblyRange147 (n : ℕ) (now : NoDescendingTail n)
    (rest : ∀ a : ℕ, n+1 ≤ a → a ≤ 147 → NoDescendingTail a)
    (a : ℕ) (low : n ≤ a) (high : a ≤ 147) : NoDescendingTail a := by
  by_cases e : a = n
  · subst a
    exact now
  · exact rest a (by omega) high

/-- Both arithmetic dispatch and the real bridge are elaborated before any of the
concrete certificates are imported. The first arguments are just propositions. -/
theorem genericAssembly147
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
    (s138 : NoDescendingTail 138)
    (s139 : NoDescendingTail 139)
    (s140 : NoDescendingTail 140)
    (s141 : NoDescendingTail 141)
    (s142 : NoDescendingTail 142)
    (s143 : NoDescendingTail 143)
    (s144 : NoDescendingTail 144)
    (s145 : NoDescendingTail 145)
    (s146 : NoDescendingTail 146)
    (s147 : NoDescendingTail 147)
    (w : Fin 9 → ℝ) (hpos : ∀ i, 0 < w i)
    (sep : ∀ A B : Finset (Fin 9), A ≠ B →
      1 ≤ |(∑ i ∈ A, w i) - (∑ i ∈ B, w i)|) :
    ∃ i, 149 ≤ w i := by
  apply separated_nine_at_least_149_of_remaining_tails _ w hpos sep
  intro a hlo hhi
  by_cases low : a ≤ 122
  · exact through122 a hlo low
  · exact (prependAssemblyRange147 123 s123 (
      prependAssemblyRange147 124 s124 (
      prependAssemblyRange147 125 s125 (
      prependAssemblyRange147 126 s126 (
      prependAssemblyRange147 127 s127 (
      prependAssemblyRange147 128 s128 (
      prependAssemblyRange147 129 s129 (
      prependAssemblyRange147 130 s130 (
      prependAssemblyRange147 131 s131 (
      prependAssemblyRange147 132 s132 (
      prependAssemblyRange147 133 s133 (
      prependAssemblyRange147 134 s134 (
      prependAssemblyRange147 135 s135 (
      prependAssemblyRange147 136 s136 (
      prependAssemblyRange147 137 s137 (
      prependAssemblyRange147 138 s138 (
      prependAssemblyRange147 139 s139 (
      prependAssemblyRange147 140 s140 (
      prependAssemblyRange147 141 s141 (
      prependAssemblyRange147 142 s142 (
      prependAssemblyRange147 143 s143 (
      prependAssemblyRange147 144 s144 (
      prependAssemblyRange147 145 s145 (
      prependAssemblyRange147 146 s146 (
      prependAssemblyRange147 147 s147 (
      emptyAssemblyRange147)))))))))))))))))))))))))) a (by omega) hhi

#print axioms genericAssembly147
end NineSeparatedSubsetSums

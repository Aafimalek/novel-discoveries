import EulerAllUsedNonLex
import EulerAllUsedProfilePreserved

namespace LatinGap.PairEncoding
open EulerAllUsedDiagrams

/-- The actual size-17 all-used geometric case reduces to satisfying
an exact archived initial clause segment. This segment stops before
the final free-label lexicographic symmetry run. No satisfiability
or refutation claim is made for the whole original CNF. -/
theorem allUsed_geometry_nonLex {D : Design 6} (lin : Linear D) (sat : Saturated D)
    (size : D.card=17) (min : ∀ x : Label 6, 2 ≤ freq D x)
    (allused : ∀ (i j : Coord) (a b : Fin 6), i ≠ j →
      freq D (i,a)=2 → freq D (j,b)=2 → Used D (i,a) (j,b)) :
    ∃ (G : Design 6) (W : Coord → Word 6) (v : ℕ → Bool),
      Linear G ∧ Saturated G ∧ G.card=17 ∧ actualRowCodes W ∈ published ∧
      (∀ (g : Coord) (a : Fin 6), freq G (g,a) = if a=0 then 2 else 3) ∧
      AllUsedPinCommon G W v ∧
      ∀ c ∈ archiveAllUsedNonLex (actualRowCodes W), NumberedHolds v c := by
  have existsWord : ∃ a : Word 6, a ∈ D ∧ ∀ j, freq D (j,a j) = 2 := by
    have someLow (j : Coord) := minimum_two_has_low size min j
    choose a ha using someLow
    exact ⟨a,all_used_low_word lin a ha (fun i j ne => allused i j (a i) (a j) ne (ha i) (ha j)),ha⟩
  obtain ⟨a,ha,afreq⟩ := existsWord
  have initial (g : Coord) (b : Fin 6) (ne : b ≠ a g) : freq D (g,b)=3 := by
    obtain ⟨lo,hl,hall⟩ := all_used_profile lin size min allused g
    have same : a g=lo := by
      by_contra e
      have hbad := (hall (a g) e).symm.trans (afreq g)
      exact (by decide : 3 ≠ 2) hbad
    exact hall b (fun h => ne (h.trans same.symm))
  obtain ⟨G,hG,hsG,hcG,hzG,fz,fr,W,hW,hpub⟩ :=
    all_used_realizes_published_withProfile lin sat a ha afreq initial
  have prof (g : Coord) (b : Fin 6) : freq G (g,b) = if b=0 then 2 else 3 := by
    by_cases hb : b=0
    · subst b
      simpa using fz g
    · simpa [hb] using fr g b hb
  have hc : G.card=17 := hcG.trans size
  obtain ⟨v,hv⟩ := actual_allUsed_pin_common hG hsG hc hzG prof W (fun i => (hW i).1) hpub
  exact ⟨G,W,v,hG,hsG,hc,hpub,prof,hv,actual_allUsed_nonLex_holds hG hsG v W hv prof⟩

#print axioms allUsed_geometry_nonLex
end LatinGap.PairEncoding

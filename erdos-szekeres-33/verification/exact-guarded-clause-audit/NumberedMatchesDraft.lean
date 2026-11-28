/- Uncompiled draft: intentionally not a verified addition to NumberedCNF. -/
import NumberedCNF

namespace ES33.Numbering

/-- A one-sided exact row-content relation: every required row appears
in the checked formula, possibly with a different literal order. -/
def Matches (required checked : NumberedCNF) : Prop :=
  ∀ c ∈ required, ∃ d ∈ checked, ∀ l, l ∈ c ↔ l ∈ d

theorem numberedSatisfies_of_matches (a : Nat → Bool)
    {required checked : NumberedCNF} (h : Matches required checked)
    (s : NumberedSatisfies a checked) : NumberedSatisfies a required := by
  intro c hc
  obtain ⟨d, hd, he⟩ := h c hc
  obtain ⟨l, hl, hv⟩ := s d hd
  exact ⟨l, (he l).mpr hl, hv⟩

/-- For UNSAT transport the executable checker's formula needs to be
contained in the compiled specification, not the other way around.
Literal permutation and duplicate rows do not change this reasoning. -/
theorem of_matches_numbered_unsat {V : Type} [DecidableEq V] [BEq V] [LawfulBEq V]
    (keys : List V) (F : CNF V) (covered : Supports keys F)
    (C : NumberedCNF) (h : Matches C (compile keys F covered))
    (unsat : ¬ ∃ a, NumberedSatisfies a C) :
    ¬ ∃ a, Satisfies a F := by
  intro ht
  obtain ⟨a, ha⟩ := (compile_equisat keys F covered).mpr ht
  exact unsat ⟨a, numberedSatisfies_of_matches a h ha⟩

end ES33.Numbering

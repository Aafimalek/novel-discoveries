import EulerAllUsedConditionalRefutations
import C02CoreMembers00
import C02CoreMembers01
import C02CoreMembers02
import C02CoreMembers03
import C02CoreMembers04
import C02CoreMembers05
import C02CoreMembers06
import C02CoreMembers07

set_option maxRecDepth 12000
set_option maxHeartbeats 0

namespace LatinGap.PairEncoding.C02Blocks
open Euler.C02RawFactored

theorem all_core_rows_local : ∀ c ∈ rows, c ∈ archiveAllUsedCNF codes := by
  simp only [rows, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨chunk_mem00,chunk_mem01⟩,⟨chunk_mem02,chunk_mem03⟩⟩,⟨⟨chunk_mem04,chunk_mem05⟩,⟨chunk_mem06,chunk_mem07⟩⟩⟩,⟨⟨⟨chunk_mem08,chunk_mem09⟩,⟨chunk_mem10,chunk_mem11⟩⟩,⟨⟨chunk_mem12,chunk_mem13⟩,⟨chunk_mem14,chunk_mem15⟩⟩⟩⟩,⟨⟨⟨⟨chunk_mem16,chunk_mem17⟩,⟨chunk_mem18,chunk_mem19⟩⟩,⟨⟨chunk_mem20,chunk_mem21⟩,⟨chunk_mem22,chunk_mem23⟩⟩⟩,⟨⟨⟨chunk_mem24,chunk_mem25⟩,⟨chunk_mem26,chunk_mem27⟩⟩,⟨⟨chunk_mem28,chunk_mem29⟩,⟨chunk_mem30,chunk_mem31⟩⟩⟩⟩⟩

/-- The numbered formula emitted by the geometry for C02 has no model. -/
theorem c02_no_numbered_archive_model :
    ¬ ∃ v : ℕ → Bool, ∀ c ∈ archiveAllUsedCNF codes, NumberedHolds v c := by
  rintro ⟨v,hv⟩
  have h := numberedFormula_sat_forward v rows (fun c hc => hv c (all_core_rows_local c hc))
  change (dimacsSatValuation v).satisfies_fmla (mapFormula rows) at h
  rw [rows_match_checked_core] at h
  exact Euler.Batch.C02.coreUnsat _ h

/-- An actual all-used design must be represented by a published case other than C02. -/
theorem allUsed_geometry_except_c02 {D : Design 6} (lin : Linear D)
    (sat : Saturated D) (size : D.card=17) (min : ∀ x : Label 6, 2 ≤ freq D x)
    (allused : ∀ (i j : Coord) (a b : Fin 6), i ≠ j →
      freq D (i,a)=2 → freq D (j,b)=2 → Used D (i,a) (j,b)) :
    ∃ cs ∈ remainingAllUsedDiagrams [codes], ∃ v : ℕ → Bool,
      ∀ c ∈ archiveAllUsedCNF cs, NumberedHolds v c := by
  refine allUsed_geometry_only_remaining lin sat size min allused [codes] ?_
  intro cs hcs
  have heq : cs = codes := List.mem_singleton.mp hcs
  subst cs
  exact c02_no_numbered_archive_model

#print axioms all_core_rows_local
#print axioms c02_no_numbered_archive_model
#print axioms allUsed_geometry_except_c02
end LatinGap.PairEncoding.C02Blocks

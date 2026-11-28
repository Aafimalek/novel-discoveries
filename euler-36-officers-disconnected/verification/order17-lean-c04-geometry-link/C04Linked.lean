import EulerAllUsedConditionalRefutations
import C04CoreMembers00
import C04CoreMembers01
import C04CoreMembers02
import C04CoreMembers03
import C04CoreMembers04
import C04CoreMembers05
import C04CoreMembers06
import C04CoreMembers07
import C04CoreMembers08
import C04CoreMembers09
import C04CoreMembers10
import C04CoreMembers11
import C04CoreMembers12
import C04CoreMembers13
import C04CoreMembers14
import C04CoreMembers15

set_option maxRecDepth 12000
set_option maxHeartbeats 0

namespace LatinGap.PairEncoding.C04Linked
open Euler.C04RawFactored

theorem all_core_rows_local : ∀ c ∈ rows, c ∈ archiveAllUsedCNF codes := by
  simp only [rows, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨chunk_mem00,chunk_mem01⟩,⟨chunk_mem02,chunk_mem03⟩⟩,⟨⟨chunk_mem04,chunk_mem05⟩,⟨chunk_mem06,chunk_mem07⟩⟩⟩,⟨⟨⟨chunk_mem08,chunk_mem09⟩,⟨chunk_mem10,chunk_mem11⟩⟩,⟨⟨chunk_mem12,chunk_mem13⟩,⟨chunk_mem14,chunk_mem15⟩⟩⟩⟩,⟨⟨⟨⟨chunk_mem16,chunk_mem17⟩,⟨chunk_mem18,chunk_mem19⟩⟩,⟨⟨chunk_mem20,chunk_mem21⟩,⟨chunk_mem22,chunk_mem23⟩⟩⟩,⟨⟨⟨chunk_mem24,chunk_mem25⟩,⟨chunk_mem26,chunk_mem27⟩⟩,⟨⟨chunk_mem28,chunk_mem29⟩,⟨chunk_mem30,chunk_mem31⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨chunk_mem32,chunk_mem33⟩,⟨chunk_mem34,chunk_mem35⟩⟩,⟨⟨chunk_mem36,chunk_mem37⟩,⟨chunk_mem38,chunk_mem39⟩⟩⟩,⟨⟨⟨chunk_mem40,chunk_mem41⟩,⟨chunk_mem42,chunk_mem43⟩⟩,⟨⟨chunk_mem44,chunk_mem45⟩,⟨chunk_mem46,chunk_mem47⟩⟩⟩⟩,⟨⟨⟨⟨chunk_mem48,chunk_mem49⟩,⟨chunk_mem50,chunk_mem51⟩⟩,⟨⟨chunk_mem52,chunk_mem53⟩,⟨chunk_mem54,chunk_mem55⟩⟩⟩,⟨⟨⟨chunk_mem56,chunk_mem57⟩,⟨chunk_mem58,chunk_mem59⟩⟩,⟨⟨chunk_mem60,chunk_mem61⟩,⟨chunk_mem62,chunk_mem63⟩⟩⟩⟩⟩⟩

/-- The numbered formula emitted by the geometry for C04 has no model. -/
theorem c04_no_numbered_archive_model :
    ¬ ∃ v : ℕ → Bool, ∀ c ∈ archiveAllUsedCNF codes, NumberedHolds v c := by
  rintro ⟨v,hv⟩
  have h := numberedFormula_sat_forward v rows (fun c hc => hv c (all_core_rows_local c hc))
  change (dimacsSatValuation v).satisfies_fmla (mapFormula rows) at h
  rw [rows_match_checked_core] at h
  exact Euler.Batch.C04.coreUnsat _ h

/-- An actual all-used design must be represented by a published case other than C04. -/
theorem allUsed_geometry_except_c04 {D : Design 6} (lin : Linear D)
    (sat : Saturated D) (size : D.card=17) (min : ∀ x : Label 6, 2 ≤ freq D x)
    (allused : ∀ (i j : Coord) (a b : Fin 6), i ≠ j →
      freq D (i,a)=2 → freq D (j,b)=2 → Used D (i,a) (j,b)) :
    ∃ cs ∈ remainingAllUsedDiagrams [codes], ∃ v : ℕ → Bool,
      ∀ c ∈ archiveAllUsedCNF cs, NumberedHolds v c := by
  refine allUsed_geometry_only_remaining lin sat size min allused [codes] ?_
  intro cs hcs
  have heq : cs = codes := List.mem_singleton.mp hcs
  subst cs
  exact c04_no_numbered_archive_model

#print axioms all_core_rows_local
#print axioms c04_no_numbered_archive_model
#print axioms allUsed_geometry_except_c04
end LatinGap.PairEncoding.C04Linked

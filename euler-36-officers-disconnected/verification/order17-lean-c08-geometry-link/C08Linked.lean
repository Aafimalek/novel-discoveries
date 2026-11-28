import C08RawFactored
import EulerAllUsedConditionalRefutations
import C08CoreMembers00
import C08CoreMembers01
import C08CoreMembers02
import C08CoreMembers03
import C08CoreMembers04
import C08CoreMembers05
import C08CoreMembers06
import C08CoreMembers07
import C08CoreMembers08
import C08CoreMembers09
import C08CoreMembers10
import C08CoreMembers11
import C08CoreMembers12
import C08CoreMembers13
import C08CoreMembers14
import C08CoreMembers15
import C08CoreMembers16
import C08CoreMembers17
import C08CoreMembers18
import C08CoreMembers19
import C08CoreMembers20
import C08CoreMembers21
import C08CoreMembers22
import C08CoreMembers23
import C08CoreMembers24
import C08CoreMembers25
import C08CoreMembers26
import C08CoreMembers27
import C08CoreMembers28
import C08CoreMembers29
import C08CoreMembers30
import C08CoreMembers31

set_option maxRecDepth 12000
set_option maxHeartbeats 0

namespace LatinGap.PairEncoding.C08Linked
open Euler.C08RawFactored

theorem all_core_rows_local : ∀ c ∈ rows, c ∈ archiveAllUsedCNF codes := by
  simp only [rows, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨chunk_mem00,chunk_mem01⟩,⟨chunk_mem02,chunk_mem03⟩⟩,⟨⟨chunk_mem04,chunk_mem05⟩,⟨chunk_mem06,chunk_mem07⟩⟩⟩,⟨⟨⟨chunk_mem08,chunk_mem09⟩,⟨chunk_mem10,chunk_mem11⟩⟩,⟨⟨chunk_mem12,chunk_mem13⟩,⟨chunk_mem14,chunk_mem15⟩⟩⟩⟩,⟨⟨⟨⟨chunk_mem16,chunk_mem17⟩,⟨chunk_mem18,chunk_mem19⟩⟩,⟨⟨chunk_mem20,chunk_mem21⟩,⟨chunk_mem22,chunk_mem23⟩⟩⟩,⟨⟨⟨chunk_mem24,chunk_mem25⟩,⟨chunk_mem26,chunk_mem27⟩⟩,⟨⟨chunk_mem28,chunk_mem29⟩,⟨chunk_mem30,chunk_mem31⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨chunk_mem32,chunk_mem33⟩,⟨chunk_mem34,chunk_mem35⟩⟩,⟨⟨chunk_mem36,chunk_mem37⟩,⟨chunk_mem38,chunk_mem39⟩⟩⟩,⟨⟨⟨chunk_mem40,chunk_mem41⟩,⟨chunk_mem42,chunk_mem43⟩⟩,⟨⟨chunk_mem44,chunk_mem45⟩,⟨chunk_mem46,chunk_mem47⟩⟩⟩⟩,⟨⟨⟨⟨chunk_mem48,chunk_mem49⟩,⟨chunk_mem50,chunk_mem51⟩⟩,⟨⟨chunk_mem52,chunk_mem53⟩,⟨chunk_mem54,chunk_mem55⟩⟩⟩,⟨⟨⟨chunk_mem56,chunk_mem57⟩,⟨chunk_mem58,chunk_mem59⟩⟩,⟨⟨chunk_mem60,chunk_mem61⟩,⟨chunk_mem62,chunk_mem63⟩⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨⟨chunk_mem64,chunk_mem65⟩,⟨chunk_mem66,chunk_mem67⟩⟩,⟨⟨chunk_mem68,chunk_mem69⟩,⟨chunk_mem70,chunk_mem71⟩⟩⟩,⟨⟨⟨chunk_mem72,chunk_mem73⟩,⟨chunk_mem74,chunk_mem75⟩⟩,⟨⟨chunk_mem76,chunk_mem77⟩,⟨chunk_mem78,chunk_mem79⟩⟩⟩⟩,⟨⟨⟨⟨chunk_mem80,chunk_mem81⟩,⟨chunk_mem82,chunk_mem83⟩⟩,⟨⟨chunk_mem84,chunk_mem85⟩,⟨chunk_mem86,chunk_mem87⟩⟩⟩,⟨⟨⟨chunk_mem88,chunk_mem89⟩,⟨chunk_mem90,chunk_mem91⟩⟩,⟨⟨chunk_mem92,chunk_mem93⟩,⟨chunk_mem94,chunk_mem95⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨chunk_mem96,chunk_mem97⟩,⟨chunk_mem98,chunk_mem99⟩⟩,⟨⟨chunk_mem100,chunk_mem101⟩,⟨chunk_mem102,chunk_mem103⟩⟩⟩,⟨⟨⟨chunk_mem104,chunk_mem105⟩,⟨chunk_mem106,chunk_mem107⟩⟩,⟨⟨chunk_mem108,chunk_mem109⟩,⟨chunk_mem110,chunk_mem111⟩⟩⟩⟩,⟨⟨⟨⟨chunk_mem112,chunk_mem113⟩,⟨chunk_mem114,chunk_mem115⟩⟩,⟨⟨chunk_mem116,chunk_mem117⟩,⟨chunk_mem118,chunk_mem119⟩⟩⟩,⟨⟨⟨chunk_mem120,chunk_mem121⟩,⟨chunk_mem122,chunk_mem123⟩⟩,⟨⟨chunk_mem124,chunk_mem125⟩,⟨chunk_mem126,chunk_mem127⟩⟩⟩⟩⟩⟩⟩

/-- The numbered formula emitted by the geometry for C08 has no model. -/
theorem c08_no_numbered_archive_model :
    ¬ ∃ v : ℕ → Bool, ∀ c ∈ archiveAllUsedCNF codes, NumberedHolds v c := by
  rintro ⟨v,hv⟩
  have h := numberedFormula_sat_forward v rows (fun c hc => hv c (all_core_rows_local c hc))
  change (dimacsSatValuation v).satisfies_fmla (mapFormula rows) at h
  rw [rows_match_checked_core] at h
  exact Euler.Batch.C08.coreUnsat _ h

/-- An actual all-used design must be represented by a published case other than C08. -/
theorem allUsed_geometry_except_c08 {D : Design 6} (lin : Linear D)
    (sat : Saturated D) (size : D.card=17) (min : ∀ x : Label 6, 2 ≤ freq D x)
    (allused : ∀ (i j : Coord) (a b : Fin 6), i ≠ j →
      freq D (i,a)=2 → freq D (j,b)=2 → Used D (i,a) (j,b)) :
    ∃ cs ∈ remainingAllUsedDiagrams [codes], ∃ v : ℕ → Bool,
      ∀ c ∈ archiveAllUsedCNF cs, NumberedHolds v c := by
  refine allUsed_geometry_only_remaining lin sat size min allused [codes] ?_
  intro cs hcs
  have heq : cs = codes := List.mem_singleton.mp hcs
  subst cs
  exact c08_no_numbered_archive_model

#print axioms all_core_rows_local
#print axioms c08_no_numbered_archive_model
#print axioms allUsed_geometry_except_c08
end LatinGap.PairEncoding.C08Linked

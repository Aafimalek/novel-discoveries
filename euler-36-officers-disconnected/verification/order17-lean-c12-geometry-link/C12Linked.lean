import C12RawFactored
import EulerAllUsedConditionalRefutations
import C12CoreMembers00
import C12CoreMembers01
import C12CoreMembers02
import C12CoreMembers03
import C12CoreMembers04
import C12CoreMembers05
import C12CoreMembers06
import C12CoreMembers07
import C12CoreMembers08
import C12CoreMembers09
import C12CoreMembers10
import C12CoreMembers11
import C12CoreMembers12
import C12CoreMembers13
import C12CoreMembers14
import C12CoreMembers15
import C12CoreMembers16
import C12CoreMembers17
import C12CoreMembers18
import C12CoreMembers19
import C12CoreMembers20
import C12CoreMembers21
import C12CoreMembers22
import C12CoreMembers23
import C12CoreMembers24
import C12CoreMembers25
import C12CoreMembers26
import C12CoreMembers27
import C12CoreMembers28
import C12CoreMembers29
import C12CoreMembers30
import C12CoreMembers31
import C12CoreMembers32
import C12CoreMembers33
import C12CoreMembers34
import C12CoreMembers35
import C12CoreMembers36
import C12CoreMembers37
import C12CoreMembers38
import C12CoreMembers39
import C12CoreMembers40
import C12CoreMembers41
import C12CoreMembers42
import C12CoreMembers43
import C12CoreMembers44
import C12CoreMembers45
import C12CoreMembers46
import C12CoreMembers47
import C12CoreMembers48
import C12CoreMembers49
import C12CoreMembers50
import C12CoreMembers51
import C12CoreMembers52
import C12CoreMembers53
import C12CoreMembers54
import C12CoreMembers55
import C12CoreMembers56
import C12CoreMembers57
import C12CoreMembers58
import C12CoreMembers59
import C12CoreMembers60
import C12CoreMembers61
import C12CoreMembers62
import C12CoreMembers63

set_option maxRecDepth 12000
set_option maxHeartbeats 0

namespace LatinGap.PairEncoding.C12Linked
open Euler.C12RawFactored

theorem all_core_rows_local : ∀ c ∈ rows, c ∈ archiveAllUsedCNF codes := by
  simp only [rows, List.forall_mem_append]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨chunk_mem00,chunk_mem01⟩,⟨chunk_mem02,chunk_mem03⟩⟩,⟨⟨chunk_mem04,chunk_mem05⟩,⟨chunk_mem06,chunk_mem07⟩⟩⟩,⟨⟨⟨chunk_mem08,chunk_mem09⟩,⟨chunk_mem10,chunk_mem11⟩⟩,⟨⟨chunk_mem12,chunk_mem13⟩,⟨chunk_mem14,chunk_mem15⟩⟩⟩⟩,⟨⟨⟨⟨chunk_mem16,chunk_mem17⟩,⟨chunk_mem18,chunk_mem19⟩⟩,⟨⟨chunk_mem20,chunk_mem21⟩,⟨chunk_mem22,chunk_mem23⟩⟩⟩,⟨⟨⟨chunk_mem24,chunk_mem25⟩,⟨chunk_mem26,chunk_mem27⟩⟩,⟨⟨chunk_mem28,chunk_mem29⟩,⟨chunk_mem30,chunk_mem31⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨chunk_mem32,chunk_mem33⟩,⟨chunk_mem34,chunk_mem35⟩⟩,⟨⟨chunk_mem36,chunk_mem37⟩,⟨chunk_mem38,chunk_mem39⟩⟩⟩,⟨⟨⟨chunk_mem40,chunk_mem41⟩,⟨chunk_mem42,chunk_mem43⟩⟩,⟨⟨chunk_mem44,chunk_mem45⟩,⟨chunk_mem46,chunk_mem47⟩⟩⟩⟩,⟨⟨⟨⟨chunk_mem48,chunk_mem49⟩,⟨chunk_mem50,chunk_mem51⟩⟩,⟨⟨chunk_mem52,chunk_mem53⟩,⟨chunk_mem54,chunk_mem55⟩⟩⟩,⟨⟨⟨chunk_mem56,chunk_mem57⟩,⟨chunk_mem58,chunk_mem59⟩⟩,⟨⟨chunk_mem60,chunk_mem61⟩,⟨chunk_mem62,chunk_mem63⟩⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨⟨chunk_mem64,chunk_mem65⟩,⟨chunk_mem66,chunk_mem67⟩⟩,⟨⟨chunk_mem68,chunk_mem69⟩,⟨chunk_mem70,chunk_mem71⟩⟩⟩,⟨⟨⟨chunk_mem72,chunk_mem73⟩,⟨chunk_mem74,chunk_mem75⟩⟩,⟨⟨chunk_mem76,chunk_mem77⟩,⟨chunk_mem78,chunk_mem79⟩⟩⟩⟩,⟨⟨⟨⟨chunk_mem80,chunk_mem81⟩,⟨chunk_mem82,chunk_mem83⟩⟩,⟨⟨chunk_mem84,chunk_mem85⟩,⟨chunk_mem86,chunk_mem87⟩⟩⟩,⟨⟨⟨chunk_mem88,chunk_mem89⟩,⟨chunk_mem90,chunk_mem91⟩⟩,⟨⟨chunk_mem92,chunk_mem93⟩,⟨chunk_mem94,chunk_mem95⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨chunk_mem96,chunk_mem97⟩,⟨chunk_mem98,chunk_mem99⟩⟩,⟨⟨chunk_mem100,chunk_mem101⟩,⟨chunk_mem102,chunk_mem103⟩⟩⟩,⟨⟨⟨chunk_mem104,chunk_mem105⟩,⟨chunk_mem106,chunk_mem107⟩⟩,⟨⟨chunk_mem108,chunk_mem109⟩,⟨chunk_mem110,chunk_mem111⟩⟩⟩⟩,⟨⟨⟨⟨chunk_mem112,chunk_mem113⟩,⟨chunk_mem114,chunk_mem115⟩⟩,⟨⟨chunk_mem116,chunk_mem117⟩,⟨chunk_mem118,chunk_mem119⟩⟩⟩,⟨⟨⟨chunk_mem120,chunk_mem121⟩,⟨chunk_mem122,chunk_mem123⟩⟩,⟨⟨chunk_mem124,chunk_mem125⟩,⟨chunk_mem126,chunk_mem127⟩⟩⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨⟨⟨chunk_mem128,chunk_mem129⟩,⟨chunk_mem130,chunk_mem131⟩⟩,⟨⟨chunk_mem132,chunk_mem133⟩,⟨chunk_mem134,chunk_mem135⟩⟩⟩,⟨⟨⟨chunk_mem136,chunk_mem137⟩,⟨chunk_mem138,chunk_mem139⟩⟩,⟨⟨chunk_mem140,chunk_mem141⟩,⟨chunk_mem142,chunk_mem143⟩⟩⟩⟩,⟨⟨⟨⟨chunk_mem144,chunk_mem145⟩,⟨chunk_mem146,chunk_mem147⟩⟩,⟨⟨chunk_mem148,chunk_mem149⟩,⟨chunk_mem150,chunk_mem151⟩⟩⟩,⟨⟨⟨chunk_mem152,chunk_mem153⟩,⟨chunk_mem154,chunk_mem155⟩⟩,⟨⟨chunk_mem156,chunk_mem157⟩,⟨chunk_mem158,chunk_mem159⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨chunk_mem160,chunk_mem161⟩,⟨chunk_mem162,chunk_mem163⟩⟩,⟨⟨chunk_mem164,chunk_mem165⟩,⟨chunk_mem166,chunk_mem167⟩⟩⟩,⟨⟨⟨chunk_mem168,chunk_mem169⟩,⟨chunk_mem170,chunk_mem171⟩⟩,⟨⟨chunk_mem172,chunk_mem173⟩,⟨chunk_mem174,chunk_mem175⟩⟩⟩⟩,⟨⟨⟨⟨chunk_mem176,chunk_mem177⟩,⟨chunk_mem178,chunk_mem179⟩⟩,⟨⟨chunk_mem180,chunk_mem181⟩,⟨chunk_mem182,chunk_mem183⟩⟩⟩,⟨⟨⟨chunk_mem184,chunk_mem185⟩,⟨chunk_mem186,chunk_mem187⟩⟩,⟨⟨chunk_mem188,chunk_mem189⟩,⟨chunk_mem190,chunk_mem191⟩⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨⟨chunk_mem192,chunk_mem193⟩,⟨chunk_mem194,chunk_mem195⟩⟩,⟨⟨chunk_mem196,chunk_mem197⟩,⟨chunk_mem198,chunk_mem199⟩⟩⟩,⟨⟨⟨chunk_mem200,chunk_mem201⟩,⟨chunk_mem202,chunk_mem203⟩⟩,⟨⟨chunk_mem204,chunk_mem205⟩,⟨chunk_mem206,chunk_mem207⟩⟩⟩⟩,⟨⟨⟨⟨chunk_mem208,chunk_mem209⟩,⟨chunk_mem210,chunk_mem211⟩⟩,⟨⟨chunk_mem212,chunk_mem213⟩,⟨chunk_mem214,chunk_mem215⟩⟩⟩,⟨⟨⟨chunk_mem216,chunk_mem217⟩,⟨chunk_mem218,chunk_mem219⟩⟩,⟨⟨chunk_mem220,chunk_mem221⟩,⟨chunk_mem222,chunk_mem223⟩⟩⟩⟩⟩,⟨⟨⟨⟨⟨chunk_mem224,chunk_mem225⟩,⟨chunk_mem226,chunk_mem227⟩⟩,⟨⟨chunk_mem228,chunk_mem229⟩,⟨chunk_mem230,chunk_mem231⟩⟩⟩,⟨⟨⟨chunk_mem232,chunk_mem233⟩,⟨chunk_mem234,chunk_mem235⟩⟩,⟨⟨chunk_mem236,chunk_mem237⟩,⟨chunk_mem238,chunk_mem239⟩⟩⟩⟩,⟨⟨⟨⟨chunk_mem240,chunk_mem241⟩,⟨chunk_mem242,chunk_mem243⟩⟩,⟨⟨chunk_mem244,chunk_mem245⟩,⟨chunk_mem246,chunk_mem247⟩⟩⟩,⟨⟨⟨chunk_mem248,chunk_mem249⟩,⟨chunk_mem250,chunk_mem251⟩⟩,⟨⟨chunk_mem252,chunk_mem253⟩,⟨chunk_mem254,chunk_mem255⟩⟩⟩⟩⟩⟩⟩⟩

/-- The numbered formula emitted by the geometry for C12 has no model. -/
theorem c12_no_numbered_archive_model :
    ¬ ∃ v : ℕ → Bool, ∀ c ∈ archiveAllUsedCNF codes, NumberedHolds v c := by
  rintro ⟨v,hv⟩
  have h := numberedFormula_sat_forward v rows (fun c hc => hv c (all_core_rows_local c hc))
  change (dimacsSatValuation v).satisfies_fmla (mapFormula rows) at h
  rw [rows_match_checked_core] at h
  exact Euler.Batch.C12.coreUnsat _ h

/-- An actual all-used design must be represented by a published case other than C12. -/
theorem allUsed_geometry_except_c12 {D : Design 6} (lin : Linear D)
    (sat : Saturated D) (size : D.card=17) (min : ∀ x : Label 6, 2 ≤ freq D x)
    (allused : ∀ (i j : Coord) (a b : Fin 6), i ≠ j →
      freq D (i,a)=2 → freq D (j,b)=2 → Used D (i,a) (j,b)) :
    ∃ cs ∈ remainingAllUsedDiagrams [codes], ∃ v : ℕ → Bool,
      ∀ c ∈ archiveAllUsedCNF cs, NumberedHolds v c := by
  refine allUsed_geometry_only_remaining lin sat size min allused [codes] ?_
  intro cs hcs
  have heq : cs = codes := List.mem_singleton.mp hcs
  subst cs
  exact c12_no_numbered_archive_model

#print axioms all_core_rows_local
#print axioms c12_no_numbered_archive_model
#print axioms allUsed_geometry_except_c12
end LatinGap.PairEncoding.C12Linked

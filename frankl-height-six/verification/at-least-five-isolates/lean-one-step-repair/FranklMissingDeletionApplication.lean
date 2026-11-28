import FranklMissingDeletionHeight
import FranklLowFrequency

/- Kernel-checked with pinned Lean 4.36 and Mathlib. -/
namespace FranklForcingFiber
variable {α : Type*} [DecidableEq α]

/-- A height-preserving one-set repair for a subfamily with one doubled
frequency excess of one and every other doubled deficit positive. -/
theorem exists_weak_repair_of_one_excess
    {G B : Finset (Finset α)} {x : α} {T : Finset α}
    (hG : NoStrictMajority G) (hBG : B ⊆ G) (hB : UnionClosed B)
    (hTG : T ∈ G) (hT : ∀ ⦃D⦄, D ∈ B → D ⊂ T)
    (hxLow : B.card < 2 * frequency B x)
    (hxHigh : 2 * frequency B x ≤ B.card + 1)
    (hothers : ∀ v, v ≠ x → 2 * frequency B v + 1 ≤ B.card) :
    ∃ H : Finset (Finset α), NoStrictMajority H ∧ ground H ⊆ ground B := by
  classical
  obtain ⟨A,hAB,hxA,he,hmax⟩ := exists_maximal_missing_erase hxLow
  let H := insert (A.erase x) B
  have hANE : (A.erase x).Nonempty := by
    by_contra hn
    have he0 := Finset.not_nonempty_iff_eq_empty.mp hn
    have hA : A = {x} := by
      calc
        A = insert x (A.erase x) := (Finset.insert_erase hxA).symm
        _ = {x} := by rw [he0]; rfl
    exact weak_no_singleton hG x (hA ▸ hBG hAB)
  refine ⟨H, ⟨⟨A.erase x,Finset.mem_insert_self _ _⟩,?_,
    unionClosed_insert_maximal_missing_erase hB hAB hmax,
    noSevenChain_insert_erase_of_extra_top hG.2.2.2.1 hBG hB hAB hxA hTG hT,
    repaired_insert_weak_frequencies he (Finset.notMem_erase x A) hxHigh hothers⟩,?_⟩
  · intro D hD
    rcases Finset.mem_insert.mp hD with rfl | hD
    · exact hANE
    · exact hG.2.1 (hBG hD)
  · apply Finset.sup_le
    intro D hD
    rcases Finset.mem_insert.mp hD with rfl | hD
    · exact (Finset.erase_subset _ _).trans (subset_ground hAB)
    · exact subset_ground hD

/-- Endpoint API for the exactly-four-isolates one-source case: the
15-trace classifier only needs to provide these exact fiber frequencies.
We do not assert or import a formal proof of that classifier here. -/
theorem no_containing_profile_fifteen_seven_eight
    {G : Finset (Finset α)} {p x : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hp : p ∈ ground G)
    (hP : (G.filter (p ∈ ·)).card = 15)
    (hxP : frequency (G.filter (p ∈ ·)) x = 7)
    (hHigh : ∀ v ∈ ground G, v ≠ x →
      8 ≤ frequency (G.filter (p ∈ ·)) v) : False := by
  classical
  let P := G.filter (p ∈ ·)
  let B := G.filter (p ∉ ·)
  have hBG : B ⊆ G := fun A ha => (Finset.mem_filter.mp ha).1
  have hne : B.Nonempty := ⟨avoid G p,
    Finset.mem_filter.mpr ⟨avoid_mem_weak hG p,notMem_avoid G p⟩⟩
  have hB : UnionClosed B := by
    intro A D ha hd
    obtain ⟨haG,hpa⟩ := Finset.mem_filter.mp ha
    obtain ⟨hdG,hpd⟩ := Finset.mem_filter.mp hd
    exact Finset.mem_filter.mpr ⟨hG.2.2.1 haG hdG,
      fun h => (Finset.mem_union.mp h).elim hpa hpd⟩
  have hsmall : ground B ⊆ (ground G).erase p := by
    apply Finset.sup_le
    intro A ha w hw
    have hnot : p ∉ A := (Finset.mem_filter.mp ha).2
    exact Finset.mem_erase.mpr ⟨fun e => hnot (e ▸ hw),subset_ground (hBG ha) hw⟩
  have hsmallCard : (ground B).card < (ground G).card :=
    (Finset.card_le_card hsmall).trans_lt (Finset.card_lt_card (Finset.erase_ssubset hp))
  have hT : ∀ ⦃A⦄, A ∈ B → A ⊂ ground G := by
    intro A ha
    have hn : p ∉ A := (Finset.mem_filter.mp ha).2
    exact Finset.ssubset_iff_subset_ne.mpr
      ⟨subset_ground (hBG ha),fun e => hn (e.symm ▸ hp)⟩
  have hpart : P.card + B.card = G.card := Finset.card_filter_add_card_filter_not (p ∈ ·)
  change P.card = 15 at hP
  change frequency P x = 7 at hxP
  have hxHigh : 2 * frequency B x ≤ B.card + 1 := by
    have he := frequency_partition_by_point G p x
    change frequency P x + frequency B x = frequency G x at he
    have h := hG.2.2.2.2 x
    omega
  have hothers : ∀ v, v ≠ x → 2 * frequency B v + 1 ≤ B.card := by
    intro v hvx
    by_cases hv : v ∈ ground G
    · have hs := hHigh v hv hvx
      change 8 ≤ frequency P v at hs
      have he := frequency_partition_by_point G p v
      change frequency P v + frequency B v = frequency G v at he
      have h := hG.2.2.2.2 v
      omega
    · have hz : frequency B v = 0 := frequency_eq_zero_of_notMem_ground
        (fun h => hv (Finset.mem_of_mem_erase (hsmall h)))
      have hb : 0 < B.card := Finset.card_pos.mpr hne
      omega
  have hxLow : B.card < 2 * frequency B x := by
    by_contra hn
    have hWeak : NoStrictMajority B := by
      refine ⟨hne,fun _ ha => hG.2.1 (hBG ha),hB,?_,?_⟩
      · intro A D E F H I J ha hd he hf hh hi hj
        exact hG.2.2.2.1 (hBG ha) (hBG hd) (hBG he) (hBG hf) (hBG hh) (hBG hi) (hBG hj)
      · intro v
        by_cases e : v = x
        · subst v
          omega
        · have h := hothers v e
          omega
    exact (Nat.not_le_of_lt hsmallCard) (hmin B hWeak)
  obtain ⟨H,hH,hHB⟩ := exists_weak_repair_of_one_excess hG hBG hB
    (ground_mem_weak hG) hT hxLow hxHigh hothers
  exact (Nat.not_le_of_lt ((Finset.card_le_card hHB).trans_lt hsmallCard)) (hmin H hH)

#print axioms exists_weak_repair_of_one_excess
#print axioms no_containing_profile_fifteen_seven_eight
end FranklForcingFiber

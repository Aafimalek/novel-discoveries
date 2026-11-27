import FranklTerminalPairGeometry
import FranklStarIndex

namespace FranklForcingFiber
variable {α : Type*} [DecidableEq α]

theorem frequency_partition_by_point (G : Finset (Finset α)) (p y : α) :
    frequency (G.filter (p ∈ ·)) y + frequency (G.filter (p ∉ ·)) y = frequency G y := by
  unfold frequency
  have hL : (G.filter (p ∈ ·)).filter (y ∈ ·) = (G.filter (y ∈ ·)).filter (p ∈ ·) := by
    ext A
    simp only [Finset.mem_filter]
    tauto
  have hR : (G.filter (p ∉ ·)).filter (y ∈ ·) = (G.filter (y ∈ ·)).filter (p ∉ ·) := by
    ext A
    simp only [Finset.mem_filter]
    tauto
  rw [hL,hR]
  exact Finset.card_filter_add_card_filter_not (p ∈ ·)

theorem frequency_eq_zero_of_notMem_ground {G : Finset (Finset α)} {x : α}
    (h : x ∉ ground G) : frequency G x = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro A ha
  obtain ⟨hA,hx⟩ := Finset.mem_filter.mp ha
  exact h (subset_ground hA hx)

/-- A weak ground-minimal counterexample has no point appearing just once or
twice. Deleting the containing fiber loses at most two sets, including the
top, so the half bound survives for all retained points. -/
theorem weakMinimalGround_frequency_ge_three {G : Finset (Finset α)} {p : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G) (hp : p ∈ ground G) :
    3 ≤ frequency G p := by
  by_contra! hfreq
  let P := G.filter (p ∈ ·)
  let F := G.filter (p ∉ ·)
  have hf : P.card ≤ 2 := by change frequency G p ≤ 2; omega
  have hcard : P.card + F.card = G.card := Finset.card_filter_add_card_filter_not (p ∈ ·)
  have hGF : ground F ⊆ (ground G).erase p := by
    apply Finset.sup_le
    intro A hA
    obtain ⟨hAG,hnA⟩ := Finset.mem_filter.mp hA
    intro y hy
    exact Finset.mem_erase.mpr ⟨fun e => hnA (e ▸ hy), subset_ground hAG hy⟩
  have ht : ground G ∈ P := Finset.mem_filter.mpr ⟨ground_mem_weak hG, hp⟩
  have hF : NoStrictMajority F := by
    have hn : F.Nonempty := ⟨avoid G p, Finset.mem_filter.mpr ⟨avoid_mem_weak hG p, notMem_avoid G p⟩⟩
    refine ⟨hn, ?_, ?_, ?_, ?_⟩
    · intro A hA
      exact hG.2.1 (Finset.mem_filter.mp hA).1
    · intro A B hA hB
      obtain ⟨hA',hnA⟩ := Finset.mem_filter.mp hA
      obtain ⟨hB',hnB⟩ := Finset.mem_filter.mp hB
      exact Finset.mem_filter.mpr ⟨hG.2.2.1 hA' hB',
        fun h => (Finset.mem_union.mp h).elim hnA hnB⟩
    · intro A B C D E F' H ha hb hc hd he hf' hh
      exact hG.2.2.2.1 (Finset.mem_filter.mp ha).1 (Finset.mem_filter.mp hb).1
        (Finset.mem_filter.mp hc).1 (Finset.mem_filter.mp hd).1 (Finset.mem_filter.mp he).1
        (Finset.mem_filter.mp hf').1 (Finset.mem_filter.mp hh).1
    · intro y
      by_cases hy : y ∈ ground G
      · have hpos : 0 < frequency P y := Finset.card_pos.mpr
          ⟨ground G, Finset.mem_filter.mpr ⟨ht,hy⟩⟩
        have he := frequency_partition_by_point G p y
        change frequency P y + frequency F y = frequency G y at he
        have hfG := hG.2.2.2.2 y
        omega
      · have hny : y ∉ ground F := fun h => hy (Finset.mem_of_mem_erase (hGF h))
        rw [frequency_eq_zero_of_notMem_ground hny, Nat.mul_zero]
        exact Nat.zero_le _
  have hmin' := hmin F hF
  have hle := Finset.card_le_card hGF
  exact (Nat.not_lt_of_ge (hmin'.trans hle)) (Finset.card_lt_card (Finset.erase_ssubset hp))

/-- A unique source and a unique isolated point are impossible. Every
source-containing member is determined entirely by its isolated coordinate. -/
theorem no_unique_source_unique_isolate {G : Finset (Finset α)} {p x : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hp : p ∈ sources G) (_hx : x ∈ isolated G)
    (hpUnique : ∀ q ∈ sources G, q = p) (hxUnique : ∀ y ∈ isolated G, y = x) : False := by
  have hpG := (mem_sources.mp hp).1
  let P := G.filter (p ∈ ·)
  have hFit : P ⊆ {ground G, (ground G).erase x} := by
    intro A hA
    obtain ⟨hAG,hpA⟩ := Finset.mem_filter.mp hA
    have hAll : (ground G).erase x ⊆ A := by
      intro y hy
      obtain ⟨hyx,hyG⟩ := Finset.mem_erase.mp hy
      by_cases hl : y ∈ leaves G
      · obtain ⟨q,hq,hqy,hF⟩ := (mem_leaves.mp hl).2
        have hqS : q ∈ sources G := mem_sources.mpr ⟨hq, y, hqy,hF⟩
        have heq := hpUnique q hqS
        exact hF hAG (heq.symm ▸ hpA)
      · by_cases hs : y ∈ sources G
        · exact (hpUnique y hs).symm ▸ hpA
        · have hi : y ∈ isolated G := Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨hyG,hl⟩,hs⟩
          exact False.elim (hyx (hxUnique y hi))
    have hAU := subset_ground hAG
    by_cases hxA : x ∈ A
    · have he : A = ground G := by
        apply Finset.Subset.antisymm hAU
        intro y hy
        by_cases h : y = x
        · exact h.symm ▸ hxA
        · exact hAll (Finset.mem_erase.mpr ⟨h,hy⟩)
      exact Finset.mem_insert.mpr (Or.inl he)
    · have he : A = (ground G).erase x := Finset.Subset.antisymm
        (fun y hy => Finset.mem_erase.mpr ⟨fun e => hxA (e ▸ hy), hAU hy⟩) hAll
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr he))
  have hcap := Finset.card_le_card hFit
  have htwo := Finset.card_insert_le (s := {(ground G).erase x}) (ground G)
  rw [Finset.card_singleton] at htwo
  have hminfreq : 3 ≤ P.card := weakMinimalGround_frequency_ge_three hG hmin hpG
  omega

#print axioms weakMinimalGround_frequency_ge_three
#print axioms no_unique_source_unique_isolate

end FranklForcingFiber

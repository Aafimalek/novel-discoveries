import FranklTerminalPairGeometry

namespace FranklForcingFiber
variable {α : Type*} [DecidableEq α]

private theorem mem_iff_of_trace_singleton {S A : Finset α} {x y : α}
    (h : S ∩ A = {x}) (hy : y ∈ S) : y ∈ A ↔ y = x := by
  constructor
  · intro ha
    have hh : y ∈ S ∩ A := Finset.mem_inter.mpr ⟨hy, ha⟩
    simpa [h] using hh
  · rintro rfl
    have hh : y ∈ S ∩ A := by rw [h]; simp
    exact (Finset.mem_inter.mp hh).2

private theorem strict_union_of_notMem_mem {A B : Finset α} {x : α}
    (ha : x ∉ A) (hb : x ∈ B) : A ⊂ A ∪ B := by
  refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_union_left, ?_⟩
  intro e
  exact ha (e.symm ▸ Finset.mem_union_right A hb)

/-- A shattered four-set builds a five-member chain by cumulatively
unioning the empty-trace witness with the four singleton-trace witnesses. -/
theorem shatter_card_le_three {G : Finset (Finset α)} {S : Finset α}
    (hU : UnionClosed G) (hH : NoFiveChain G) (hS : G.Shatters S) : S.card ≤ 3 := by
  by_contra! hlarge
  obtain ⟨w, hw⟩ := Finset.card_pos.mp (show 0 < S.card by omega)
  have hcard := Finset.card_erase_add_one hw
  obtain ⟨x, y, z, hx', hy', hz', hxy, hxz, hyz⟩ :=
    Finset.two_lt_card_iff.mp (show 2 < (S.erase w).card by omega)
  obtain ⟨hxw, hx⟩ := Finset.mem_erase.mp hx'
  obtain ⟨hyw, hy⟩ := Finset.mem_erase.mp hy'
  obtain ⟨hzw, hz⟩ := Finset.mem_erase.mp hz'
  obtain ⟨N, hN, hn⟩ := hS (Finset.empty_subset S)
  obtain ⟨A, hA, ha⟩ := hS.exists_inter_eq_singleton hx
  obtain ⟨B, hB, hb⟩ := hS.exists_inter_eq_singleton hy
  obtain ⟨C, hC, hc⟩ := hS.exists_inter_eq_singleton hz
  obtain ⟨D, hD, hd⟩ := hS.exists_inter_eq_singleton hw
  have hEmpty (u : α) (hu : u ∈ S) : u ∉ N := by
    intro h
    have hh : u ∈ S ∩ N := Finset.mem_inter.mpr ⟨hu, h⟩
    simp [hn] at hh
  have h1 : N ⊂ N ∪ A := strict_union_of_notMem_mem (hEmpty x hx) ((mem_iff_of_trace_singleton ha hx).2 rfl)
  have h2 : N ∪ A ⊂ (N ∪ A) ∪ B := by
    apply strict_union_of_notMem_mem (x := y) ?_ ((mem_iff_of_trace_singleton hb hy).2 rfl)
    simp only [Finset.mem_union, not_or]
    exact ⟨hEmpty y hy, fun h => hxy ((mem_iff_of_trace_singleton ha hy).1 h).symm⟩
  have h3 : (N ∪ A) ∪ B ⊂ ((N ∪ A) ∪ B) ∪ C := by
    apply strict_union_of_notMem_mem (x := z) ?_ ((mem_iff_of_trace_singleton hc hz).2 rfl)
    simp only [Finset.mem_union, not_or]
    exact ⟨⟨hEmpty z hz, fun h => hxz ((mem_iff_of_trace_singleton ha hz).1 h).symm⟩,
      fun h => hyz ((mem_iff_of_trace_singleton hb hz).1 h).symm⟩
  have h4 : ((N ∪ A) ∪ B) ∪ C ⊂ (((N ∪ A) ∪ B) ∪ C) ∪ D := by
    apply strict_union_of_notMem_mem (x := w) ?_ ((mem_iff_of_trace_singleton hd hw).2 rfl)
    simp only [Finset.mem_union, not_or]
    exact ⟨⟨⟨hEmpty w hw, fun h => hxw ((mem_iff_of_trace_singleton ha hw).1 h).symm⟩,
      fun h => hyw ((mem_iff_of_trace_singleton hb hw).1 h).symm⟩,
      fun h => hzw ((mem_iff_of_trace_singleton hc hw).1 h).symm⟩
  exact hH hN (hU hN hA) (hU (hU hN hA) hB) (hU (hU (hU hN hA) hB) hC)
    (hU (hU (hU (hU hN hA) hB) hC) hD) h1 h2 h3 h4

/-- Sauer's bound for union-closed families of height four. -/
theorem card_le_height_four {G : Finset (Finset α)} (T : Finset α)
    (hU : UnionClosed G) (hH : NoFiveChain G) (hT : ∀ ⦃A⦄, A ∈ G → A ⊆ T) :
    G.card ≤ 1 + T.card + T.card.choose 2 + T.card.choose 3 := by
  let D₀ := T.powersetCard 0
  let D₁ := T.powersetCard 1
  let D₂ := T.powersetCard 2
  let D₃ := T.powersetCard 3
  have hsub : G.shatterer ⊆ ((D₀ ∪ D₁) ∪ D₂) ∪ D₃ := by
    intro S hS
    have hs := Finset.mem_shatterer.mp hS
    have hsmall := shatter_card_le_three hU hH hs
    obtain ⟨A, ha, hsa⟩ := hs.exists_superset
    have hst := hsa.trans (hT ha)
    have he : S.card = 0 ∨ S.card = 1 ∨ S.card = 2 ∨ S.card = 3 := by omega
    rcases he with h | h | h | h
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl
        (Finset.mem_union.mpr (Or.inl (Finset.mem_powersetCard.mpr ⟨hst, h⟩))))))
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl
        (Finset.mem_union.mpr (Or.inr (Finset.mem_powersetCard.mpr ⟨hst, h⟩))))))
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
        (Or.inr (Finset.mem_powersetCard.mpr ⟨hst, h⟩))))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_powersetCard.mpr ⟨hst, h⟩))
  have h₀ := Finset.card_le_card_shatterer G
  have h₁ := Finset.card_le_card hsub
  have h₂ := Finset.card_union_le ((D₀ ∪ D₁) ∪ D₂) D₃
  have h₃ := Finset.card_union_le (D₀ ∪ D₁) D₂
  have h₄ := Finset.card_union_le D₀ D₁
  have he₀ : D₀.card = 1 := by simp [D₀]
  have he₁ : D₁.card = T.card := by simp [D₁, Finset.card_powersetCard]
  have he₂ : D₂.card = T.card.choose 2 := Finset.card_powersetCard _ _
  have he₃ : D₃.card = T.card.choose 3 := Finset.card_powersetCard _ _
  omega

/-- Every terminal-pair maximum must have enough support for the height-four
bound to accommodate at least n−1 pair-avoiding members. -/
theorem terminal_pair_support_card_bound {G : Finset (Finset α)} {s t : α}
    (hG : NoStrictMajority G) (hsep : Separated G)
    (hs : s ∈ ground G) (ht : t ∈ ground G) (hts : t ≠ s)
    (hsT : Terminal G s) (htT : Terminal G t) :
    (ground G).card ≤ 2 + (ground (avoidBoth G s t)).card +
      (ground (avoidBoth G s t)).card.choose 2 + (ground (avoidBoth G s t)).card.choose 3 := by
  have hN := terminal_pair_avoidance_card hG hsep hs ht hts hsT htT
  have h5 := terminal_pair_fiber_noFiveChain hG hs hts hsT htT
  have hb := card_le_height_four (ground (avoidBoth G s t))
    (cross_pair_unionClosed hG.2.2.1) h5 (fun _ hA => subset_ground hA)
  omega

#print axioms shatter_card_le_three
#print axioms card_le_height_four
#print axioms terminal_pair_support_card_bound

end FranklForcingFiber

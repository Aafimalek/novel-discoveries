import FranklForcingFiber

namespace FranklForcingFiber

variable {α : Type*} [DecidableEq α]

/-- An avoidance maximum in a ground-minimal counterexample omits
at most its avoided coordinate and its distinct proper predecessor. -/
theorem card_omitted_single_avoid_le_two {G : Finset (Finset α)}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G) (v : α) :
    ((ground G) \ avoid G v).card ≤ 2 := by
  by_contra! h
  obtain ⟨a,b,c,ha,hb,hc,hab,hac,hbc⟩ := Finset.two_lt_card_iff.mp h
  have distinct {x y : α} (hx : x ∈ ground G \ avoid G v)
      (hy : y ∈ ground G \ avoid G v) (hxv : x ≠ v) (hyv : y ≠ v) : x = y := by
    obtain ⟨hxg,hxno⟩ := Finset.mem_sdiff.mp hx
    obtain ⟨hyg,hyno⟩ := Finset.mem_sdiff.mp hy
    exact weakMinimalGround_unique_proper_predecessor hG hmin hxg hyg hxv hyv
      ((notMem_avoid_iff_forces G v x).mp hxno)
      ((notMem_avoid_iff_forces G v y).mp hyno)
  by_cases hav : a = v
  · exact hbc (distinct hb hc (fun he => hab (hav.trans he.symm)) (fun he => hac (hav.trans he.symm)))
  · by_cases hbv : b = v
    · exact hac (distinct ha hc hav (fun he => hbc (hbv.trans he.symm)))
    · exact hab (distinct ha hb hav hbv)

/-- Any extra members containing both selected terminal points and omitting
at least three points increase the lower bound on the pair-avoidance fiber. -/
theorem terminal_pair_avoidance_extra {G R : Finset (Finset α)} {s t : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hs : s ∈ ground G) (ht : t ∈ ground G) (hts : t ≠ s)
    (hsT : Terminal G s) (htT : Terminal G t)
    (hR : ∀ ⦃A⦄, A ∈ R → A ∈ G ∧ s ∈ A ∧ t ∈ A ∧ 2 < ((ground G) \ A).card) :
    (ground G).card + R.card ≤ (avoidBoth G s t).card + 1 := by
  classical
  let V := ((ground G).erase s).erase t
  let P := G.filter (fun A => s ∈ A ∧ t ∈ A)
  let B := insert (ground G) (V.image (avoid G))
  have hsep := weakMinimalGround_separated hG hmin
  have hV (v : α) (hv : v ∈ V) : v ∈ ground G ∧ v ≠ s ∧ v ≠ t := by
    obtain ⟨hvt,hv'⟩ := Finset.mem_erase.mp hv
    obtain ⟨hvs,hvg⟩ := Finset.mem_erase.mp hv'
    exact ⟨hvg,hvs,hvt⟩
  have hsubB : B ⊆ P := by
    intro A hA
    rcases Finset.mem_insert.mp hA with rfl | hi
    · exact Finset.mem_filter.mpr ⟨ground_mem_weak hG,hs,ht⟩
    · obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hi
      obtain ⟨_,hvs,hvt⟩ := hV v hv
      have h1 : s ∈ avoid G v := by
        by_contra hn
        exact hvs (hsT ((notMem_avoid_iff_forces G v s).mp hn))
      have h2 : t ∈ avoid G v := by
        by_contra hn
        exact hvt (htT ((notMem_avoid_iff_forces G v t).mp hn))
      exact Finset.mem_filter.mpr ⟨avoid_mem_weak hG v,h1,h2⟩
  have hsubR : R ⊆ P := by
    intro A ha
    obtain ⟨h1,h2,h3,_⟩ := hR ha
    exact Finset.mem_filter.mpr ⟨h1,h2,h3⟩
  have hd : Disjoint B R := by
    apply Finset.disjoint_left.mpr
    intro A hb hr
    have h3 := (hR hr).2.2.2
    rcases Finset.mem_insert.mp hb with rfl | hmem
    · simp at h3
    · obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp hmem
      exact (Nat.not_lt_of_ge (card_omitted_single_avoid_le_two hG hmin v)) h3
  have hbni : ground G ∉ V.image (avoid G) := by
    intro hb
    obtain ⟨v,hv,he⟩ := Finset.mem_image.mp hb
    exact notMem_avoid G v (he.symm ▸ (hV v hv).1)
  have hinj : Set.InjOn (avoid G) (V : Set α) := by
    intro a ha b hb h
    exact avoid_injOn_ground hsep (hV a ha).1 (hV b hb).1 h
  have hbcard : B.card = V.card + 1 := by
    dsimp [B]
    rw [Finset.card_insert_of_notMem hbni,Finset.card_image_of_injOn hinj]
  have hc := Finset.card_le_card (Finset.union_subset hsubB hsubR)
  rw [Finset.card_union_of_disjoint hd,hbcard] at hc
  have hV0 := Finset.card_erase_add_one hs
  have hV1 := Finset.card_erase_add_one (Finset.mem_erase.mpr ⟨hts,ht⟩)
  change V.card + 1 = ((ground G).erase s).card at hV1
  have hPN : P.card ≤ (avoidBoth G s t).card :=
    both_count_le_neither_count (hG.2.2.2.2 s) (hG.2.2.2.2 t)
  omega

#print axioms card_omitted_single_avoid_le_two
#print axioms terminal_pair_avoidance_extra

end FranklForcingFiber

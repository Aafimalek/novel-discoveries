import FranklSharedIsolate

namespace FranklForcingFiber
variable {α : Type*} [DecidableEq α]

/-- Extra family members containing both terminals strengthen their avoidance
count as long as they are distinct from the canonical top and one-point maxima. -/
theorem terminal_pair_avoidance_extra_noncanonical {G R : Finset (Finset α)} {s t : α}
    (hG : NoStrictMajority G) (hsep : Separated G)
    (hs : s ∈ ground G) (ht : t ∈ ground G) (hts : t ≠ s)
    (hsT : Terminal G s) (htT : Terminal G t)
    (hR : ∀ ⦃A⦄, A ∈ R → A ∈ G ∧ s ∈ A ∧ t ∈ A ∧
      A ≠ ground G ∧ ∀ v ∈ ground G, A ≠ avoid G v) :
    (ground G).card + R.card ≤ (avoidBoth G s t).card + 1 := by
  classical
  let V := ((ground G).erase s).erase t
  let P := G.filter (fun A => s ∈ A ∧ t ∈ A)
  let B := insert (ground G) (V.image (avoid G))
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
  have hsubR : R ⊆ P := fun A ha =>
    Finset.mem_filter.mpr ⟨(hR ha).1,(hR ha).2.1,(hR ha).2.2.1⟩
  have hd : Disjoint B R := by
    apply Finset.disjoint_left.mpr
    intro A hb hr
    obtain ⟨_,_,_,hne,hv⟩ := hR hr
    rcases Finset.mem_insert.mp hb with rfl | hi
    · exact hne rfl
    · obtain ⟨v,hiv,hev⟩ := Finset.mem_image.mp hi
      exact hv v (hV v hiv).1 hev.symm
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

/-- When there is a unique isolate, the source–isolate co-pairs each supply
an extra both-containing member for every pair of distinct leaves. -/
theorem one_isolate_leaf_pair_avoidance_extra {G : Finset (Finset α)} {s t x : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hs : s ∈ leaves G) (ht : t ∈ leaves G) (hts : t ≠ s)
    (hx : x ∈ isolated G) (hunique : ∀ y ∈ isolated G, y = x) :
    (ground G).card + (sources G).card ≤ (avoidBoth G s t).card + 1 := by
  classical
  let g (p : α) := ((ground G).erase p).erase x
  let R := (sources G).image g
  have hsep := weakMinimalGround_separated hG hmin
  have hxG := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hx).1).1
  have hxNS := (Finset.mem_sdiff.mp hx).2
  have hxNL := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hx).1).2
  have hinj : Set.InjOn g (sources G : Set α) := by
    intro p hp q hq he
    by_contra hne
    have hqx : q ≠ x := fun e => hxNS (e ▸ hq)
    have hqmem : q ∈ g p := Finset.mem_erase.mpr
      ⟨hqx,Finset.mem_erase.mpr ⟨(Ne.symm hne),(mem_sources.mp hq).1⟩⟩
    exact (Finset.notMem_erase _ _) (Finset.mem_of_mem_erase (he ▸ hqmem))
  have hRc : R.card = (sources G).card := Finset.card_image_of_injOn hinj
  have hleaf_terminal {z : α} (hz : z ∈ leaves G) : Terminal G z := by
    obtain ⟨p,hp,hne,hF⟩ := (mem_leaves.mp hz).2
    intro y hf
    by_contra hny
    exact noThreeForcingChain_of_separated hG hsep hp hne (Ne.symm hny) hF hf
  have hR : ∀ ⦃A⦄, A ∈ R → A ∈ G ∧ s ∈ A ∧ t ∈ A ∧
      A ≠ ground G ∧ ∀ v ∈ ground G, A ≠ avoid G v := by
    intro A ha
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ha
    have hpG := (mem_sources.mp hp).1
    have hpNL := (Finset.mem_sdiff.mp (sources_subset_nonleaf hG hmin hp)).2
    have hpx : p ≠ x := fun e => hxNS (e ▸ hp)
    have hL (z : α) (hz : z ∈ leaves G) : z ∈ g p :=
      Finset.mem_erase.mpr ⟨fun e => hxNL (e ▸ hz),Finset.mem_erase.mpr
        ⟨fun e => hpNL (e ▸ hz),(mem_leaves.mp hz).1⟩⟩
    refine ⟨source_isolate_coPair_of_unique_isolate hG hmin hp hunique,hL s hs,hL t ht,?_,?_⟩
    · intro he
      exact Finset.notMem_erase _ _ (show x ∈ g p from he.symm ▸ hxG)
    · intro v hv he
      have hvN : v ∉ g p := fun h => notMem_avoid G v (he ▸ h)
      by_cases hvp : v = p
      · subst v
        have hxN : x ∉ avoid G p := by
          intro h
          exact Finset.notMem_erase _ _ (show x ∈ g p from he.symm ▸ h)
        exact hpx (isolated_avoider_terminal hx ((notMem_avoid_iff_forces G p x).mp hxN))
      · by_cases hvx : v = x
        · subst v
          have hpN : p ∉ avoid G x := by
            intro h
            exact Finset.notMem_erase _ _ (Finset.mem_of_mem_erase (show p ∈ g p from he.symm ▸ h))
          exact hxNL (mem_leaves.mpr ⟨hxG,p,hpG,hpx,(notMem_avoid_iff_forces G x p).mp hpN⟩)
        · exact hvN (Finset.mem_erase.mpr ⟨hvx,Finset.mem_erase.mpr ⟨hvp,hv⟩⟩)
  have h := terminal_pair_avoidance_extra_noncanonical hG hsep (mem_leaves.mp hs).1
    (mem_leaves.mp ht).1 hts (hleaf_terminal hs) (hleaf_terminal ht) hR
  omega

#print axioms terminal_pair_avoidance_extra_noncanonical
#print axioms one_isolate_leaf_pair_avoidance_extra

end FranklForcingFiber

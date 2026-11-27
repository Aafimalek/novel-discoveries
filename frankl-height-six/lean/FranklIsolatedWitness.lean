import FranklProjection

namespace FranklForcingFiber
variable {α : Type*} [DecidableEq α]

theorem frequency_le_of_forces {G : Finset (Finset α)} {x y : α}
    (h : Forces G x y) : frequency G x ≤ frequency G y := by
  apply Finset.card_le_card
  intro A ha
  obtain ⟨hAG, hx⟩ := Finset.mem_filter.mp ha
  exact Finset.mem_filter.mpr ⟨hAG, h hAG hx⟩

theorem forces_restrictFamily {G : Finset (Finset α)} {S : Finset α} {x y : α}
    (hy : y ∈ S) (h : Forces G x y) : Forces (restrictFamily G S) x y := by
  intro A ha hx
  obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp ha
  exact Finset.mem_inter.mpr ⟨h hB (Finset.mem_inter.mp hx).1, hy⟩

theorem source_erase_injOn_leaf_avoiders {G : Finset (Finset α)} {p x : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hp : p ∈ sources G) (hx : x ∈ leaves G) :
    Set.InjOn (· ∩ (ground G).erase p) ((G.filter (x ∉ ·)) : Set (Finset α)) := by
  obtain ⟨hpG, s, hps, hFp⟩ := mem_sources.mp hp
  obtain ⟨q, hqG, hqx, hFq⟩ := (mem_leaves.mp hx).2
  intro A ha B hb he
  obtain ⟨hAG, hAx⟩ := Finset.mem_filter.mp ha
  obtain ⟨hBG, hBx⟩ := Finset.mem_filter.mp hb
  change A ∩ (ground G).erase p = B ∩ (ground G).erase p at he
  have heq (z : α) (hz : z ∈ (ground G).erase p) : z ∈ A ↔ z ∈ B :=
    ⟨fun h => (Finset.mem_inter.mp (he ▸ Finset.mem_inter.mpr ⟨h, hz⟩)).1,
     fun h => (Finset.mem_inter.mp (he.symm ▸ Finset.mem_inter.mpr ⟨h, hz⟩)).1⟩
  ext z
  by_cases hzp : z = p
  · subst z
    by_cases hqp : q = p
    · subst q
      exact ⟨fun h => False.elim (hAx (hFq hAG h)), fun h => False.elim (hBx (hFq hBG h))⟩
    · have hA := local_twins_across_stars hG hmin hqG hpG hqx hps hqp hFq hFp hAG hAx
      have hB := local_twins_across_stars hG hmin hqG hpG hqx hps hqp hFq hFp hBG hBx
      have hs : s ∈ (ground G).erase p := Finset.mem_erase.mpr ⟨hps.symm, mem_ground_of_forces hpG hFp⟩
      exact hA.trans ((heq s hs).trans hB.symm)
  · by_cases hz : z ∈ ground G
    · exact heq z (Finset.mem_erase.mpr ⟨hzp, hz⟩)
    · exact ⟨fun h => False.elim (hz (subset_ground hAG h)), fun h => False.elim (hz (subset_ground hBG h))⟩

/-- Removing a center cannot make any retained leaf the strict majority.
Every such majority certifies an isolated point instead. -/
theorem exists_isolated_majority_after_source_erasure {G : Finset (Finset α)} {p : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G) (hp : p ∈ sources G) :
    ∃ x ∈ isolated G, (restrictFamily G ((ground G).erase p)).card <
      2 * frequency (restrictFamily G ((ground G).erase p)) x := by
  classical
  let S := (ground G).erase p
  let F := restrictFamily G S
  have hpG := (mem_sources.mp hp).1
  have hpNotLeaf : p ∉ leaves G :=
    (Finset.mem_sdiff.mp (sources_subset_nonleaf hG hmin hp)).2
  have hLeaves (x : α) (hx : x ∈ leaves G) : x ∈ S := by
    exact Finset.mem_erase.mpr ⟨fun e => hpNotLeaf (e ▸ hx), (mem_leaves.mp hx).1⟩
  have hLeafHalf (x : α) (hx : x ∈ leaves G) : 2 * frequency F x ≤ F.card :=
    restrictFamily_frequency_le_half (hLeaves x hx)
      (source_erase_injOn_leaf_avoiders hG hmin hp hx) (hG.2.2.2.2 x)
  have hSourced (x : α) (hx : x ∈ sources G) : 2 * frequency F x ≤ F.card := by
    have hxG := (mem_sources.mp hx).1
    obtain ⟨hne, hf⟩ := starLeaf_spec hx
    have hy : starLeaf G x ∈ leaves G := mem_leaves.mpr
      ⟨mem_ground_of_forces hxG hf, x, hxG, hne, hf⟩
    have hmono := frequency_le_of_forces (forces_restrictFamily (hLeaves _ hy) hf)
    change frequency F x ≤ frequency F (starLeaf G x) at hmono
    have hhalf := hLeafHalf _ hy
    omega
  by_contra hnone
  have hAll (x : α) : 2 * frequency F x ≤ F.card := by
    by_cases hx : x ∈ ground G
    · by_cases hl : x ∈ leaves G
      · exact hLeafHalf x hl
      · by_cases hp' : x ∈ sources G
        · exact hSourced x hp'
        · have hI : x ∈ isolated G := Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨hx, hl⟩, hp'⟩
          exact Nat.le_of_not_gt (fun h => hnone ⟨x, hI, h⟩)
    · have hzero : frequency F x = 0 := by
        apply Finset.card_eq_zero.mpr
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro A ha
        obtain ⟨hAF, hxA⟩ := Finset.mem_filter.mp ha
        have hs := restrictFamily_ground_subset (G := G) (S := S)
        exact hx (Finset.mem_of_mem_erase (hs (subset_ground hAF hxA)))
      simp [hzero]
  have hF : NoStrictMajority F := by
    refine ⟨hG.1.image _, ?_, restrictFamily_unionClosed hG.2.2.1 S,
      restrictFamily_noSevenChain hG.2.2.1 hG.2.2.2.1 S, hAll⟩
    intro A ha
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨x, hx⟩ := hG.2.1 hB
    by_cases he : x = p
    · obtain ⟨hne, hf⟩ := starLeaf_spec hp
      have hL := hf hB (he ▸ hx)
      exact ⟨_, Finset.mem_inter.mpr
        ⟨hL, Finset.mem_erase.mpr ⟨hne.symm, mem_ground_of_forces hpG hf⟩⟩⟩
    · exact ⟨x, Finset.mem_inter.mpr ⟨hx, Finset.mem_erase.mpr ⟨he, subset_ground hB hx⟩⟩⟩
  have hc := hmin F hF
  have hs := Finset.card_le_card (restrictFamily_ground_subset (G := G) (S := S))
  have hlt : S.card < (ground G).card := Finset.card_lt_card (Finset.erase_ssubset hpG)
  exact (Nat.not_lt_of_ge (hc.trans hs)) hlt

/-- For every source, there is an isolated point missed by both members of
a one-point edge in that source's coordinate; both members contain all leaves. -/
theorem source_edge_with_isolated_witness {G : Finset (Finset α)} {p : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G) (hp : p ∈ sources G) :
    ∃ x ∈ isolated G, ∃ A ∈ G, x ∉ A ∧ p ∉ A ∧ leaves G ⊆ A ∧ insert p A ∈ G := by
  classical
  let S := (ground G).erase p
  obtain ⟨x, hx, hfreq⟩ := exists_isolated_majority_after_source_erasure hG hmin hp
  have hxG := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hx).1).1
  have hxp : x ≠ p := fun e => (Finset.mem_sdiff.mp hx).2 (e.symm ▸ hp)
  have hxS : x ∈ S := Finset.mem_erase.mpr ⟨hxp, hxG⟩
  have hn : ¬ Set.InjOn (· ∩ S) ((G.filter (x ∉ ·)) : Set (Finset α)) := by
    intro hi
    exact (Nat.not_lt_of_ge (restrictFamily_frequency_le_half hxS hi (hG.2.2.2.2 x))) hfreq
  refine ⟨x, hx, ?_⟩
  by_contra hno
  apply hn
  intro A ha B hb he
  obtain ⟨hAG, hAx⟩ := Finset.mem_filter.mp ha
  obtain ⟨hBG, hBx⟩ := Finset.mem_filter.mp hb
  change A ∩ S = B ∩ S at he
  have hEqErase (C : Finset α) (hC : C ∈ G) : C ∩ S = C.erase p := by
    ext y
    constructor
    · intro h
      obtain ⟨hy, hyS⟩ := Finset.mem_inter.mp h
      exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hyS).1, hy⟩
    · intro h
      obtain ⟨hne, hy⟩ := Finset.mem_erase.mp h
      exact Finset.mem_inter.mpr ⟨hy, Finset.mem_erase.mpr ⟨hne, subset_ground hC hy⟩⟩
  have he' : A.erase p = B.erase p := (hEqErase A hAG).symm.trans (he.trans (hEqErase B hBG))
  have haux {C D : Finset α} (hCG : C ∈ G) (hDG : D ∈ G) (hCx : x ∉ C)
      (hpC : p ∉ C) (hpD : p ∈ D) (hProj : C ∩ S = D ∩ S) (heer : C.erase p = D.erase p) : False := by
    have heq := eq_insert_of_erase_of_mem heer hpD
    have hLeaves : leaves G ⊆ C := by
      intro y hy
      by_contra hyC
      have hyne : y ≠ p := by
        intro e
        exact (Finset.mem_sdiff.mp (sources_subset_nonleaf hG hmin hp)).2 (e ▸ hy)
      have hyD : y ∉ D := by
        intro h
        have hh := Finset.mem_erase.mpr ⟨hyne, h⟩
        rw [← heer] at hh
        exact hyC (Finset.mem_of_mem_erase hh)
      have hCD := source_erase_injOn_leaf_avoiders hG hmin hp hy
        (Finset.mem_filter.mpr ⟨hCG, hyC⟩) (Finset.mem_filter.mpr ⟨hDG, hyD⟩) hProj
      exact hpC (hCD.symm ▸ hpD)
    exact hno ⟨C, hCG, hCx, hpC, hLeaves, heq ▸ hDG⟩
  apply equal_of_erase_and_same_membership he'
  exact ⟨fun h => by
    by_contra h'
    exact haux hBG hAG hBx h' h he.symm he'.symm,
  fun h => by
    by_contra h'
    exact haux hAG hBG hAx h' h he he'⟩

#print axioms source_erase_injOn_leaf_avoiders
#print axioms exists_isolated_majority_after_source_erasure
#print axioms source_edge_with_isolated_witness

end FranklForcingFiber

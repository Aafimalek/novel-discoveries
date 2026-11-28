import FranklFourAmbientTrace

/- Kernel-checked on pinned Lean 4.36 and Mathlib. -/
namespace FranklForcingFiber

variable {α : Type*} [DecidableEq α]

/-- The physical preimage of the full isolate trace among source-containing
members. This definition works for any number of isolates. -/
noncomputable def fullIsolateContainingFiber (G : Finset (Finset α)) (p : α) :
    Finset (Finset α) :=
  G.filter (fun A => p ∈ A ∧ isolated G ⊆ A)

private theorem starLeaf_mem_leaves {G : Finset (Finset α)} {q : α}
    (hq : q ∈ sources G) : starLeaf G q ∈ leaves G := by
  obtain ⟨hne,hf⟩ := starLeaf_spec hq
  have hqG := (mem_sources.mp hq).1
  exact mem_leaves.mpr ⟨mem_ground_of_forces hqG hf,q,hqG,hne,hf⟩

/-- Different source stars cannot have the same chosen leaf. -/
theorem starLeaf_injOn_sources {G : Finset (Finset α)}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G) :
    Set.InjOn (starLeaf G) (sources G : Set α) := by
  intro p hp q hq he
  have hpS : p ∈ sources G := hp
  have hqS : q ∈ sources G := hq
  obtain ⟨hpne,hpF⟩ := starLeaf_spec hpS
  obtain ⟨hqne,hqF⟩ := starLeaf_spec hqS
  exact weakMinimalGround_unique_proper_predecessor hG hmin
    (mem_sources.mp hpS).1 (mem_sources.mp hqS).1 hpne (he.symm ▸ hqne)
    hpF (he.symm ▸ hqF)

/-- Fixing the containing source does not fix the other stars. The full
isolate trace has at least k physical preimages: the original top and
one different co-leaf top for each other source. -/
theorem sources_card_le_fullIsolateContainingFiber
    {G : Finset (Finset α)} {p : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hp : p ∈ sources G) :
    (sources G).card ≤ (fullIsolateContainingFiber G p).card := by
  classical
  let K := (sources G).erase p
  let f := fun q : α => avoid G (starLeaf G q)
  let W := K.image f
  let U := ground G
  have hpG : p ∈ U := (mem_sources.mp hp).1
  have hpNL : p ∉ leaves G :=
    (Finset.mem_sdiff.mp (sources_subset_nonleaf hG hmin hp)).2
  have hIsoU : isolated G ⊆ U := fun _ ha => (mem_isolated.mp ha).1
  have htop : U ∈ fullIsolateContainingFiber G p :=
    Finset.mem_filter.mpr ⟨ground_mem_weak hG,hpG,hIsoU⟩
  have hW : W ⊆ fullIsolateContainingFiber G p := by
    intro A hA
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨hqp,hqS⟩ := Finset.mem_erase.mp hq
    have hqG := (mem_sources.mp hqS).1
    obtain ⟨hqn,hF⟩ := starLeaf_spec hqS
    have hL := starLeaf_mem_leaves hqS
    have heq : f q = (U.erase q).erase (starLeaf G q) :=
      avoid_eq_coPair_of_edge hG hmin hqG hqn hF
    apply Finset.mem_filter.mpr
    refine ⟨avoid_mem_weak hG (starLeaf G q),?_,?_⟩
    · rw [heq]
      exact Finset.mem_erase.mpr
        ⟨fun e => hpNL (e.symm ▸ hL),Finset.mem_erase.mpr ⟨hqp.symm,hpG⟩⟩
    · intro a ha
      have haNL := (mem_isolated.mp ha).2.2
      have haNS := (Finset.mem_sdiff.mp ha).2
      rw [heq]
      exact Finset.mem_erase.mpr ⟨fun e => haNL (e.symm ▸ hL),
        Finset.mem_erase.mpr ⟨fun e => haNS (e.symm ▸ hqS),hIsoU ha⟩⟩
  have hnot : U ∉ W := by
    intro hU
    obtain ⟨q,hq,he⟩ := Finset.mem_image.mp hU
    have hL := starLeaf_mem_leaves (Finset.mem_of_mem_erase hq)
    have hLG := (mem_leaves.mp hL).1
    have hh : starLeaf G q ∈ f q := he.symm ▸ (show starLeaf G q ∈ U from hLG)
    exact notMem_avoid G (starLeaf G q) hh
  have hinj : Set.InjOn f (K : Set α) := by
    intro q hq r hr he
    have hqS := Finset.mem_of_mem_erase (show q ∈ K from hq)
    have hrS := Finset.mem_of_mem_erase (show r ∈ K from hr)
    have heLeaf := avoid_injOn_ground (weakMinimalGround_separated hG hmin)
      (mem_leaves.mp (starLeaf_mem_leaves hqS)).1
      (mem_leaves.mp (starLeaf_mem_leaves hrS)).1 he
    exact starLeaf_injOn_sources hG hmin hqS hrS heLeaf
  have hcard : W.card = K.card := Finset.card_image_of_injOn hinj
  have hsub : insert U W ⊆ fullIsolateContainingFiber G p := by
    intro A hA
    rcases Finset.mem_insert.mp hA with rfl | hA
    · exact htop
    · exact hW hA
  have h := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hnot,hcard] at h
  exact (Finset.card_erase_add_one hp).symm.le.trans h

/-- In the multi-source case the checked one-source trace-counting input
is false: isolate projection on the containing fiber is not injective. -/
theorem containing_trace_not_injOn_of_multiple_sources
    {G : Finset (Finset α)} {p : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hp : p ∈ sources G) (hk : 2 ≤ (sources G).card)
    (lab : FourTraceLabels (isolated G)) :
    ¬ Set.InjOn lab.trace ((G.filter (p ∈ ·)) : Set (Finset α)) := by
  intro hinj
  have htwo := hk.trans (sources_card_le_fullIsolateContainingFiber hG hmin hp)
  obtain ⟨A,D,hA,hD,hne⟩ := Finset.one_lt_card_iff.mp (show
    1 < (fullIsolateContainingFiber G p).card by omega)
  obtain ⟨haG,hpa,haI⟩ := Finset.mem_filter.mp hA
  obtain ⟨hdG,hpd,hdI⟩ := Finset.mem_filter.mp hD
  exact hne (hinj (Finset.mem_filter.mpr ⟨haG,hpa⟩) (Finset.mem_filter.mpr ⟨hdG,hpd⟩)
    ((lab.trace_eq_univ_of_subset haI).trans (lab.trace_eq_univ_of_subset hdI).symm))

#print axioms starLeaf_injOn_sources
#print axioms sources_card_le_fullIsolateContainingFiber
#print axioms containing_trace_not_injOn_of_multiple_sources
end FranklForcingFiber

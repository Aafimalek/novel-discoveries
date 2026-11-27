import FranklCrossStarPair

namespace FranklForcingFiber

variable {α : Type*} [DecidableEq α]

/-- The centers of the nontrivial outward stars. -/
noncomputable def sources (G : Finset (Finset α)) : Finset α := by
  classical
  exact (ground G).filter (fun p => ∃ s, p ≠ s ∧ Forces G p s)

theorem mem_sources {G : Finset (Finset α)} {p : α} :
    p ∈ sources G ↔ p ∈ ground G ∧ ∃ s, p ≠ s ∧ Forces G p s := by
  classical
  exact Finset.mem_filter

/-- Deterministically for the proof, select a leaf of each center. -/
noncomputable def starLeaf (G : Finset (Finset α)) (p : α) : α := by
  classical
  exact if h : p ∈ sources G then Classical.choose (mem_sources.mp h).2 else p

theorem starLeaf_spec {G : Finset (Finset α)} {p : α} (hp : p ∈ sources G) :
    p ≠ starLeaf G p ∧ Forces G p (starLeaf G p) := by
  classical
  simpa [starLeaf, hp] using Classical.choose_spec (mem_sources.mp hp).2

theorem sources_subset_nonleaf {G : Finset (Finset α)}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G) : sources G ⊆ ground G \ leaves G := by
  intro p hp
  obtain ⟨hpG,s,hps,hf⟩ := mem_sources.mp hp
  exact Finset.mem_sdiff.mpr ⟨hpG,outgoing_not_leaf hG (weakMinimalGround_separated hG hmin) hps hf⟩

theorem sources_card_le_leaves {G : Finset (Finset α)}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G) :
    (sources G).card ≤ (leaves G).card := by
  apply Finset.card_le_card_of_injOn (starLeaf G)
  · intro p hp
    have hpG := (mem_sources.mp hp).1
    have ⟨hpne,hpF⟩ := starLeaf_spec hp
    exact mem_leaves.mpr ⟨mem_ground_of_forces hpG hpF,p,hpG,hpne,hpF⟩
  · intro p hp q hq he
    have ⟨hpne,hpF⟩ := starLeaf_spec hp
    have ⟨hqne,hqF⟩ := starLeaf_spec hq
    exact weakMinimalGround_unique_proper_predecessor hG hmin
      (mem_sources.mp hp).1 (mem_sources.mp hq).1 hpne (he.symm ▸ hqne) hpF (he.symm ▸ hqF)

/-- Points that are neither leaves nor centers. -/
noncomputable def isolated (G : Finset (Finset α)) : Finset α :=
  (ground G \ leaves G) \ sources G

theorem partition_card {G : Finset (Finset α)}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G) :
    (ground G).card = (isolated G).card + (sources G).card + (leaves G).card := by
  have hL : leaves G ⊆ ground G := fun _ hx => (mem_leaves.mp hx).1
  have h1 := Finset.card_sdiff_add_card_eq_card hL
  have h2 := Finset.card_sdiff_add_card_eq_card (sources_subset_nonleaf hG hmin)
  unfold isolated
  omega

theorem pairReps_card_formula {G : Finset (Finset α)} {p q : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hp : p ∈ sources G) (hq : q ∈ sources G) (hpq : p ≠ q) :
    (pairReps G p q).card = (isolated G).card + (sources G).card - 2 := by
  obtain ⟨hps,hFp⟩ := starLeaf_spec hp
  obtain ⟨hqt,hFq⟩ := starLeaf_spec hq
  have h1 := pairReps_card_add_leaves_add_two hG (weakMinimalGround_separated hG hmin)
    (mem_sources.mp hp).1 (mem_sources.mp hq).1 hpq hps hqt hFp hFq
  have h2 := partition_card hG hmin
  omega

/-- Drop the centers in C and all of their leaves. -/
noncomputable def outsideStars (G : Finset (Finset α)) (C : Finset α) : Finset α := by
  classical
  exact (ground G).filter (fun x => ∀ p ∈ C, ¬ Forces G p x)

theorem mem_outsideStars {G : Finset (Finset α)} {C : Finset α} {x : α} :
    x ∈ outsideStars G C ↔ x ∈ ground G ∧ ∀ p ∈ C, ¬ Forces G p x := by
  classical
  exact Finset.mem_filter

theorem center_mem_outsideStars_iff {G : Finset (Finset α)} {C : Finset α} {x : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G) (hC : C ⊆ sources G)
    (hx : x ∈ sources G) : x ∈ outsideStars G C ↔ x ∉ C := by
  constructor
  · intro hout hmem
    exact (mem_outsideStars.mp hout).2 x hmem (forces_refl G x)
  · intro hxC
    refine mem_outsideStars.mpr ⟨(mem_sources.mp hx).1, ?_⟩
    intro p hp hf
    have hpx : p ≠ x := fun e => hxC (e ▸ hp)
    obtain ⟨z,hxz,hFz⟩ := (mem_sources.mp hx).2
    exact noThreeForcingChain_of_separated hG (weakMinimalGround_separated hG hmin)
      (mem_sources.mp (hC hp)).1 hpx hxz hf hFz

theorem outsideStars_inj {G : Finset (Finset α)} {C D : Finset α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hC : C ⊆ sources G) (hD : D ⊆ sources G)
    (he : outsideStars G C = outsideStars G D) : C = D := by
  ext x
  by_cases hx : x ∈ sources G
  · have h1 := center_mem_outsideStars_iff hG hmin hC hx
    have h2 := center_mem_outsideStars_iff hG hmin hD hx
    rw [he] at h1
    simpa only [not_not] using not_congr (h1.symm.trans h2)
  · have no1 : x ∉ C := fun h => hx (hC h)
    have no2 : x ∉ D := fun h => hx (hD h)
    simp [no1,no2]

theorem repLeaf_mem_outsideStars {G : Finset (Finset α)} {C : Finset α} {p : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G) (hC : C ⊆ sources G)
    (hp : p ∈ sources G) (hpC : p ∉ C) : starLeaf G p ∈ outsideStars G C := by
  have hpG := (mem_sources.mp hp).1
  obtain ⟨hpn,hpf⟩ := starLeaf_spec hp
  refine mem_outsideStars.mpr ⟨mem_ground_of_forces hpG hpf,?_⟩
  intro q hq hqf
  have hqG := (mem_sources.mp (hC hq)).1
  have hqn : q ≠ starLeaf G p := by
    intro he
    have hle : starLeaf G p ∈ leaves G := mem_leaves.mpr
      ⟨mem_ground_of_forces hpG hpf,p,hpG,hpn,hpf⟩
    exact (Finset.mem_sdiff.mp (sources_subset_nonleaf hG hmin (hC hq))).2 (he.symm ▸ hle)
  have he := weakMinimalGround_unique_proper_predecessor hG hmin hpG hqG hpn hqn hpf hqf
  exact hpC (he.symm ▸ hq)

/-- Two distinct removed centers already omit themselves and one of
their genuine leaves, hence the omitted points exceed two. -/
theorem outsideStars_omit_more_than_two {G : Finset (Finset α)} {C : Finset α} {a b : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G) (hC : C ⊆ sources G)
    (ha : a ∈ C) (hb : b ∈ C) (hab : a ≠ b) :
    2 < (ground G \ outsideStars G C).card := by
  have hA := (mem_sources.mp (hC ha)).1
  have hB := (mem_sources.mp (hC hb)).1
  obtain ⟨hane,hF⟩ := starLeaf_spec (hC ha)
  have hL := mem_ground_of_forces hA hF
  have haN : a ∉ outsideStars G C :=
    fun h => (mem_outsideStars.mp h).2 a ha (forces_refl G a)
  have hbN : b ∉ outsideStars G C :=
    fun h => (mem_outsideStars.mp h).2 b hb (forces_refl G b)
  have hlN : starLeaf G a ∉ outsideStars G C :=
    fun h => (mem_outsideStars.mp h).2 a ha hF
  have hbl : b ≠ starLeaf G a := by
    intro he
    have hx : starLeaf G a ∈ leaves G := mem_leaves.mpr ⟨hL,a,hA,hane,hF⟩
    exact (Finset.mem_sdiff.mp (sources_subset_nonleaf hG hmin (hC hb))).2 (he.symm ▸ hx)
  exact Finset.two_lt_card_iff.mpr ⟨a,b,starLeaf G a,
    Finset.mem_sdiff.mpr ⟨hA,haN⟩,Finset.mem_sdiff.mpr ⟨hB,hbN⟩,
    Finset.mem_sdiff.mpr ⟨hL,hlN⟩,hab,hane,hbl⟩

#print axioms partition_card
#print axioms pairReps_card_formula
#print axioms sources_card_le_leaves
#print axioms outsideStars_inj
#print axioms repLeaf_mem_outsideStars
#print axioms outsideStars_omit_more_than_two

end FranklForcingFiber

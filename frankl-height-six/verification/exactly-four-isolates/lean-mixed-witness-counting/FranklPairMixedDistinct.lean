import FranklPairMixedGeometry

/- Direct Lean-checked mixed-witness lemmas. -/
namespace FranklForcingFiber
variable {α : Type*} [DecidableEq α]

private theorem chosen_leaf_mem_leaves {G : Finset (Finset α)} {r : α}
    (hr : r ∈ sources G) : starLeaf G r ∈ leaves G := by
  have hrG := (mem_sources.mp hr).1
  obtain ⟨hne,hF⟩ := starLeaf_spec hr
  exact mem_leaves.mpr ⟨mem_ground_of_forces hrG hF,r,hrG,hne,hF⟩

theorem chosenStarPoints_subset_mixedOther {G : Finset (Finset α)} {r v : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hr : r ∈ sources G) (hv : v ∈ sources G) (hne : r ≠ v)
    {J : Finset α} (hJ : J ⊆ isolated G) :
    chosenStarPoints G v ⊆ mixedStarOmission G r J := by
  intro x hx
  refine Finset.mem_sdiff.mpr ⟨chosenStarPoints_subset_ground hv hx,?_⟩
  intro hh
  rcases Finset.mem_union.mp hh with hr' | hj
  · exact (Finset.disjoint_left.mp (chosenStarPoints_disjoint_of_sources hG hmin hr hv hne)) hr' hx
  · exact (Finset.disjoint_left.mp (chosenStarPoints_disjoint_isolates hv)) hx (hJ hj)

theorem chosen_leaf_mem_mixedOther {G : Finset (Finset α)} {r v : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hr : r ∈ sources G) (hv : v ∈ sources G) (hne : r ≠ v)
    {J : Finset α} (hJ : J ⊆ isolated G) :
    starLeaf G v ∈ mixedStarOmission G r J :=
  chosenStarPoints_subset_mixedOther hG hmin hr hv hne hJ
    (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))

theorem source_notMem_mixedStarOmission (G : Finset (Finset α)) (r : α) (J : Finset α) :
    r ∉ mixedStarOmission G r J := by
  intro hr
  exact (Finset.mem_sdiff.mp hr).2
    (Finset.mem_union_left _ (Finset.mem_insert_self _ _))

theorem chosen_leaf_notMem_mixedStarOmission (G : Finset (Finset α)) (r : α) (J : Finset α) :
    starLeaf G r ∉ mixedStarOmission G r J := by
  intro hr
  exact (Finset.mem_sdiff.mp hr).2
    (Finset.mem_union_left _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))

theorem mixedStarOmission_ne_ground {G : Finset (Finset α)} {r : α}
    (hr : r ∈ sources G) (J : Finset α) :
    mixedStarOmission G r J ≠ ground G := by
  intro h
  exact source_notMem_mixedStarOmission G r J (h.symm ▸ (mem_sources.mp hr).1)

/-- A nonempty isolate hole rules out being any single-point avoidance
maximum. The isolated hole would force its target to equal itself,
but the omitted source would then be its forbidden predecessor. -/
theorem mixedStarOmission_ne_avoid {G : Finset (Finset α)} {r v : α}
    (hr : r ∈ sources G) {J : Finset α}
    (hJ : J ⊆ isolated G) (hne : J.Nonempty) :
    mixedStarOmission G r J ≠ avoid G v := by
  intro he
  obtain ⟨x,hx⟩ := hne
  have hxI := hJ hx
  have hxN : x ∉ mixedStarOmission G r J := fun h =>
    (Finset.mem_sdiff.mp h).2 (Finset.mem_union_right _ hx)
  have hxA : x ∉ avoid G v := fun h => hxN (he.symm ▸ h)
  have hvx : v = x := (mem_isolated.mp hxI).2.1
    ((notMem_avoid_iff_forces G v x).mp hxA)
  subst v
  have hrA : r ∉ avoid G x := fun h => source_notMem_mixedStarOmission G r J (he.symm ▸ h)
  have hrx : r ≠ x := fun e => (Finset.mem_sdiff.mp hxI).2 (e ▸ hr)
  exact (mem_isolated.mp hxI).2.2 (mem_leaves.mpr
    ⟨(mem_isolated.mp hxI).1,r,(mem_sources.mp hr).1,hrx,
      (notMem_avoid_iff_forces G x r).mp hrA⟩)

theorem mixedStarOmission_ne_sourceWitnessTop
    {G : Finset (Finset α)} {r v : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hr : r ∈ sources G) (hv : v ∈ sources G) (J : Finset α) :
    mixedStarOmission G r J ≠ sourceWitnessTop G hG hmin v := by
  intro he
  have hL := (sourceWitnessTop_spec hG hmin hv).2.2.2.1
  exact chosen_leaf_notMem_mixedStarOmission G r J (he.symm ▸ hL (chosen_leaf_mem_leaves hr))

theorem mixedStarOmission_notMem_pairMaxima
    {G : Finset (Finset α)} {r : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hr : r ∈ sources G) {J : Finset α} (hJ : J ⊆ isolated G) :
    mixedStarOmission G r J ∉ starPairMaxima G := by
  intro h
  obtain ⟨p,hp,q,hq,hpq,he⟩ := mem_starPairMaxima.mp h
  by_cases hp' : r = p
  · have hrq : r ≠ q := fun e => hpq (hp'.symm.trans e)
    exact starPairMax_omit_right G p q
      (he.symm ▸ chosen_leaf_mem_mixedOther hG hmin hr hq hrq hJ)
  · exact starPairMax_omit_left G p q
      (he.symm ▸ chosen_leaf_mem_mixedOther hG hmin hr hp hp' hJ)

theorem mixedStarOmission_ne_of_sources_ne
    {G : Finset (Finset α)} {r v : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hr : r ∈ sources G) (hv : v ∈ sources G) (hne : r ≠ v)
    {J K : Finset α} (hK : K ⊆ isolated G) :
    mixedStarOmission G r J ≠ mixedStarOmission G v K := by
  intro he
  have hrM : r ∈ mixedStarOmission G v K :=
    chosenStarPoints_subset_mixedOther hG hmin hv hr hne.symm hK (Finset.mem_insert_self _ _)
  exact source_notMem_mixedStarOmission G r J (he.symm ▸ hrM)

/-- Different isolate holes at a fixed source also give different
physical witnesses, because source-star points are not isolates. -/
theorem mixedStarOmission_hole_injective
    {G : Finset (Finset α)} {r : α} (hr : r ∈ sources G)
    {J K : Finset α} (hJ : J ⊆ isolated G) (hK : K ⊆ isolated G)
    (he : mixedStarOmission G r J = mixedStarOmission G r K) : J = K := by
  let U := ground G
  let S := chosenStarPoints G r
  have hSG : S ⊆ U := chosenStarPoints_subset_ground hr
  have hJG : J ⊆ U := fun _ h => (mem_isolated.mp (hJ h)).1
  have hKG : K ⊆ U := fun _ h => (mem_isolated.mp (hK h)).1
  have hc := congrArg (fun X : Finset α => U \ X) he
  change U \ (U \ (S ∪ J)) = U \ (U \ (S ∪ K)) at hc
  rw [Finset.sdiff_sdiff_eq_self (Finset.union_subset hSG hJG),
    Finset.sdiff_sdiff_eq_self (Finset.union_subset hSG hKG)] at hc
  have hd := Finset.disjoint_left.mp (chosenStarPoints_disjoint_isolates hr)
  apply Finset.Subset.antisymm
  · intro x hx
    rcases Finset.mem_union.mp (hc ▸ Finset.mem_union_right S hx) with hs | hk
    · exact False.elim (hd hs (hJ hx))
    · exact hk
  · intro x hx
    rcases Finset.mem_union.mp (hc.symm ▸ Finset.mem_union_right S hx) with hs | hj
    · exact False.elim (hd hs (hK hx))
    · exact hj

#print axioms chosen_leaf_mem_mixedOther
#print axioms mixedStarOmission_ne_avoid
#print axioms mixedStarOmission_ne_sourceWitnessTop
#print axioms mixedStarOmission_notMem_pairMaxima
#print axioms mixedStarOmission_ne_of_sources_ne
#print axioms mixedStarOmission_hole_injective
end FranklForcingFiber

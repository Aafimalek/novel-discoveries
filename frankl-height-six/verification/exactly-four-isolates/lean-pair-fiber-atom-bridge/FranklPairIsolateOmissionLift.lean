import FranklPairAtomBridge

/- Kernel-checked on pinned Lean 4.36 and Mathlib. -/
namespace FranklForcingFiber
variable {α : Type*} [DecidableEq α]

/-- Isolated points are always admissible representatives. They need
not all occur in any particular pair fibre's true support. -/
theorem isolates_subset_pairReps_of_sources {G : Finset (Finset α)} {p q : α}
    (hp : p ∈ sources G) (hq : q ∈ sources G) :
    isolated G ⊆ pairReps G p q := by
  intro x hx
  have hxNoS := (Finset.mem_sdiff.mp hx).2
  obtain ⟨hxG,_,hxL⟩ := mem_isolated.mp hx
  exact mem_pairReps.mpr ⟨hxG,hxL,
    fun e => hxNoS (e.symm ▸ hp),fun e => hxNoS (e.symm ▸ hq)⟩

/-- Dropping an isolate-only omission from the true representative
support lifts to dropping exactly the same physical points from the
raw pair maximum. All unaffected whole stars remain present. -/
theorem raw_pairMax_sdiff_mem_of_isolate_atom_omission
    {G : Finset (Finset α)} {p q : α} {J : Finset α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hp : p ∈ sources G) (hq : q ∈ sources G) (hpq : p ≠ q)
    (hJI : J ⊆ isolated G) (hJ : J ∈ starPairTrueComplement G p q) :
    starPairMax G p q \ J ∈ avoidBoth G (starLeaf G p) (starLeaf G q) := by
  classical
  let T := starPairMax G p q
  let R := pairReps G p q
  have hpG := (mem_sources.mp hp).1
  have hqG := (mem_sources.mp hq).1
  obtain ⟨hps,hFp⟩ := starLeaf_spec hp
  obtain ⟨hqt,hFq⟩ := starLeaf_spec hq
  have hT : T ∈ G := starPairMax_mem_family hG hmin hp hq hpq
  have hts : starLeaf G p ∉ T := starPairMax_omit_left G p q
  obtain ⟨A,hA,hcomp⟩ := original_member_of_starPairTrueComplement hJ
  have hAG := (Finset.mem_filter.mp hA).1
  have hAT : A ⊆ T := subset_ground hA
  have hJR : J ⊆ R := hJI.trans (isolates_subset_pairReps_of_sources hp hq)
  have hEq : A ∩ R = (T ∩ R) \ J := by
    rw [compressedStarPair_ground_eq_inter] at hcomp
    exact hcomp
  have hAeq : A = T \ J := by
    apply Finset.Subset.antisymm
    · intro x hx
      refine Finset.mem_sdiff.mpr ⟨hAT hx,?_⟩
      intro hxJ
      have hz : x ∈ (T ∩ R) \ J := hEq ▸ Finset.mem_inter.mpr ⟨hx,hJR hxJ⟩
      exact (Finset.mem_sdiff.mp hz).2 hxJ
    · intro x hx
      obtain ⟨hxT,hxJ⟩ := Finset.mem_sdiff.mp hx
      have hxData := cross_pair_top_mem_outside_of_mem hG hmin hpG hqG hpq
        hps hqt hFp hFq hxT
      have hxRepImplies (hxR : x ∈ R) : x ∈ A := by
        have hz : x ∈ (T ∩ R) \ J := Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨hxT,hxR⟩,hxJ⟩
        exact (Finset.mem_inter.mp (hEq.symm ▸ hz)).1
      by_cases hxL : x ∈ leaves G
      · obtain ⟨r,hrG,hrx,hFx⟩ := (mem_leaves.mp hxL).2
        have hrp : r ≠ p := fun e => hxData.2.2.2.1 (e ▸ hFx)
        have hrq : r ≠ q := fun e => hxData.2.2.2.2 (e ▸ hFx)
        have hrS : r ∈ sources G := mem_sources.mpr ⟨hrG,x,hrx,hFx⟩
        have hrL : r ∉ leaves G :=
          (Finset.mem_sdiff.mp (sources_subset_nonleaf hG hmin hrS)).2
        have htwin := local_twins_across_stars hG hmin hpG hrG hps hrx hrp.symm hFp hFx hT hts
        have hrT : r ∈ T := htwin.mpr hxT
        have hrJ : r ∉ J := fun h => (Finset.mem_sdiff.mp (hJI h)).2 hrS
        have hrR : r ∈ R := mem_pairReps.mpr ⟨hrG,hrL,hrp,hrq⟩
        have hz : r ∈ (T ∩ R) \ J := Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨hrT,hrR⟩,hrJ⟩
        have hrA := (Finset.mem_inter.mp (hEq.symm ▸ hz)).1
        exact hFx hAG hrA
      · exact hxRepImplies (mem_pairReps.mpr ⟨hxData.1,hxL,hxData.2.1,hxData.2.2.1⟩)
  exact hAeq ▸ hA

#print axioms isolates_subset_pairReps_of_sources
#print axioms raw_pairMax_sdiff_mem_of_isolate_atom_omission
end FranklForcingFiber

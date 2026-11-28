import FranklDeficitOneManyTriples

/- Checked by pinned ordinary Lean with warnings as errors. -/
namespace FranklForcingFiber
variable {α : Type*} [DecidableEq α]

noncomputable def starPointUnion (G : Finset (Finset α)) (A : Finset α) : Finset α :=
  A.biUnion (chosenStarPoints G)

/-- The full physical complement can be read off an arbitrary omitted
block when all the stars are unary. -/
theorem ground_sdiff_pairMax_eq_starPointUnion {G : Finset (Finset α)} {p q : α}
    (hG : NoStrictMajority G) (hm : WeakMinimalGround G)
    (hp : p ∈ sources G) (hq : q ∈ sources G) (hpq : p ≠ q)
    (hUn : ∀ r ∈ sources G, UnaryAtChosenLeaf G r) :
    ground G \ starPairMax G p q =
      starPointUnion G (omittedStars G (starPairMax G p q)) ∪ (isolated G \ starPairMax G p q) := by
  classical
  let T := starPairMax G p q
  let A := omittedStars G T
  have hT : T ∈ G := starPairMax_mem_family hG hm hp hq hpq
  have hOut {r : α} (hr : r ∈ sources G) (hn : r ∉ A) : r ∈ T := by
    have hC : r ∈ ground (compressedStarPair G p q) := by
      rw [compressedStarPair_ground_eq_centers_union_present_isolates hG hm hp hq hpq]
      exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hr,hn⟩)
    exact mem_raw_ground_of_mem_compress_ground hC
  have hOmit {r : α} (hr : r ∈ A) : ∀ x ∈ chosenStarPoints G r, x ∉ T := by
    obtain ⟨hrS,hrL⟩ := mem_omittedStars.mp hr
    have hrT : r ∉ T := fun h => hrL ((starLeaf_spec hrS).2 hT h)
    intro x hx
    change x ∈ ({r,starLeaf G r} : Finset α) at hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    exact hx.elim (fun e => e.symm ▸ hrT) (fun e => e.symm ▸ hrL)
  ext x
  constructor
  · intro hx
    obtain ⟨hxG,hxT⟩ := Finset.mem_sdiff.mp hx
    by_cases hxI : x ∈ isolated G
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hxI,hxT⟩)
    · apply Finset.mem_union_left _
      by_cases hxL : x ∈ leaves G
      · obtain ⟨_,r,hrG,hrx,hFx⟩ := mem_leaves.mp hxL
        have hrS : r ∈ sources G := mem_sources.mpr ⟨hrG,x,hrx,hFx⟩
        have hrA : r ∈ A := by
          by_contra hn
          exact hxT (hFx hT (hOut hrS hn))
        have hxEq := hUn r hrS hrx hFx
        exact Finset.mem_biUnion.mpr ⟨r,hrA,
          Finset.mem_insert_of_mem (Finset.mem_singleton.mpr hxEq)⟩
      · have hxS : x ∈ sources G := by
          by_contra hn
          exact hxI (Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨hxG,hxL⟩,hn⟩)
        have hxA : x ∈ A := by
          by_contra hn
          exact hxT (hOut hxS hn)
        exact Finset.mem_biUnion.mpr ⟨x,hxA,Finset.mem_insert_self _ _⟩
  · intro hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨r,hr,hrx⟩ := Finset.mem_biUnion.mp hx
      exact Finset.mem_sdiff.mpr
        ⟨chosenStarPoints_subset_ground (mem_omittedStars.mp hr).1 hrx,hOmit hr x hrx⟩
    · exact Finset.mem_sdiff.mpr ⟨(mem_isolated.mp (Finset.mem_sdiff.mp hx).1).1,
        (Finset.mem_sdiff.mp hx).2⟩

/-- Common omitted stars of two blocks, with independent isolate holes.
Because chosen stars are disjoint and disjoint from the isolates,
intersection is computed separately in the two regions. -/
theorem intersect_starPointUnion_with_isolateHoles {G : Finset (Finset α)}
    {A B J K : Finset α}
    (hG : NoStrictMajority G) (hm : WeakMinimalGround G)
    (hA : A ⊆ sources G) (hB : B ⊆ sources G)
    (hJ : J ⊆ isolated G) (hK : K ⊆ isolated G) :
    (starPointUnion G A ∪ J) ∩ (starPointUnion G B ∪ K) =
      starPointUnion G (A ∩ B) ∪ (J ∩ K) := by
  ext x
  simp only [Finset.mem_inter,Finset.mem_union]
  constructor
  · rintro ⟨hX,hY⟩
    rcases hX with hxA | hxJ <;> rcases hY with hxB | hxK
    · obtain ⟨a,ha,hxa⟩ := Finset.mem_biUnion.mp hxA
      obtain ⟨b,hb,hxb⟩ := Finset.mem_biUnion.mp hxB
      have he : a = b := by
        by_contra hne
        exact (Finset.disjoint_left.mp (chosenStarPoints_disjoint_of_sources hG hm
          (hA ha) (hB hb) hne)) hxa hxb
      subst b
      exact Or.inl (Finset.mem_biUnion.mpr ⟨a,Finset.mem_inter.mpr ⟨ha,hb⟩,hxa⟩)
    · obtain ⟨a,ha,hxa⟩ := Finset.mem_biUnion.mp hxA
      exact False.elim ((Finset.disjoint_left.mp (chosenStarPoints_disjoint_isolates (hA ha))) hxa (hK hxK))
    · obtain ⟨b,hb,hxb⟩ := Finset.mem_biUnion.mp hxB
      exact False.elim ((Finset.disjoint_left.mp (chosenStarPoints_disjoint_isolates (hB hb))) hxb (hJ hxJ))
    · exact Or.inr ⟨hxJ,hxK⟩
  · rintro (hx | ⟨hxJ,hxK⟩)
    · obtain ⟨r,hr,hx⟩ := Finset.mem_biUnion.mp hx
      exact ⟨Or.inl (Finset.mem_biUnion.mpr ⟨r,(Finset.mem_inter.mp hr).1,hx⟩),
        Or.inl (Finset.mem_biUnion.mpr ⟨r,(Finset.mem_inter.mp hr).2,hx⟩)⟩
    · exact ⟨Or.inr hxJ,Or.inr hxK⟩

/-- Two possibly differently-sized omitted blocks intersecting only in
r give the actual mixed singleton witness at r, when each corresponding
raw top contains all isolates and admits the same isolate deletion. -/
theorem mixed_singleton_of_raw_deletions_intersecting_blocks
    {G : Finset (Finset α)} {r a b x : α}
    (hG : NoStrictMajority G) (hm : WeakMinimalGround G)
    (hr : r ∈ sources G) (ha : a ∈ sources G) (hb : b ∈ sources G)
    (hra : r ≠ a) (hrb : r ≠ b)
    (hUn : ∀ v ∈ sources G, UnaryAtChosenLeaf G v)
    (hx : x ∈ isolated G)
    (hMeet : omittedStars G (starPairMax G r a) ∩ omittedStars G (starPairMax G r b) = {r})
    (hFa : isolated G ⊆ starPairMax G r a)
    (hFb : isolated G ⊆ starPairMax G r b)
    (hXa : starPairMax G r a \ {x} ∈ avoidBoth G (starLeaf G r) (starLeaf G a))
    (hXb : starPairMax G r b \ {x} ∈ avoidBoth G (starLeaf G r) (starLeaf G b)) :
    mixedStarOmission G r {x} ∈ G := by
  let Ta := starPairMax G r a
  let Tb := starPairMax G r b
  let A := omittedStars G Ta
  let B := omittedStars G Tb
  let J : Finset α := {x}
  have hJa : J ⊆ isolated G := Finset.singleton_subset_iff.mpr hx
  have hJG : J ⊆ ground G := fun _ h => (mem_isolated.mp (hJa h)).1
  have hAG : Ta \ J ∈ G := (Finset.mem_filter.mp hXa).1
  have hBG : Tb \ J ∈ G := (Finset.mem_filter.mp hXb).1
  have hUnion := hG.2.2.1 hAG hBG
  have hA : A ⊆ sources G := fun _ h => (mem_omittedStars.mp h).1
  have hB : B ⊆ sources G := fun _ h => (mem_omittedStars.mp h).1
  have hCa : ground G \ (Ta \ J) = starPointUnion G A ∪ J := by
    rw [Finset.sdiff_sdiff_eq_sdiff_union hJG,
      ground_sdiff_pairMax_eq_starPointUnion hG hm hr ha hra hUn]
    change (starPointUnion G A ∪ (isolated G \ Ta)) ∪ J = _
    rw [Finset.sdiff_eq_empty_iff_subset.mpr hFa,Finset.union_empty]
  have hCb : ground G \ (Tb \ J) = starPointUnion G B ∪ J := by
    rw [Finset.sdiff_sdiff_eq_sdiff_union hJG,
      ground_sdiff_pairMax_eq_starPointUnion hG hm hr hb hrb hUn]
    change (starPointUnion G B ∪ (isolated G \ Tb)) ∪ J = _
    rw [Finset.sdiff_eq_empty_iff_subset.mpr hFb,Finset.union_empty]
  have hMeet' : A ∩ B = {r} := hMeet
  have hEq : ground G \ ((Ta \ J) ∪ (Tb \ J)) = chosenStarPoints G r ∪ J := by
    rw [Finset.sdiff_union_distrib,hCa,hCb,
      intersect_starPointUnion_with_isolateHoles hG hm hA hB hJa hJa,hMeet',Finset.inter_self]
    simp [starPointUnion]
  have hFinal : mixedStarOmission G r J = (Ta \ J) ∪ (Tb \ J) := by
    unfold mixedStarOmission
    rw [← hEq,Finset.sdiff_sdiff_eq_self (subset_ground hUnion)]
  exact hFinal.symm ▸ hUnion

#print axioms ground_sdiff_pairMax_eq_starPointUnion
#print axioms intersect_starPointUnion_with_isolateHoles
#print axioms mixed_singleton_of_raw_deletions_intersecting_blocks
end FranklForcingFiber

import FranklPairIsolateOmissionLift

/- Direct Lean-checked mixed-witness lemmas. -/
namespace FranklForcingFiber
variable {α : Type*} [DecidableEq α]

noncomputable def chosenStarPoints (G : Finset (Finset α)) (r : α) : Finset α :=
  {r,starLeaf G r}

def UnaryAtChosenLeaf (G : Finset (Finset α)) (r : α) : Prop :=
  ∀ ⦃v⦄, r ≠ v → Forces G r v → v = starLeaf G r

noncomputable def pairIsolateHole (G : Finset (Finset α)) (p q : α) (J : Finset α) :
    Finset α :=
  (isolated G \ starPairMax G p q) ∪ J

noncomputable def mixedStarOmission (G : Finset (Finset α)) (r : α) (J : Finset α) :
    Finset α :=
  ground G \ (chosenStarPoints G r ∪ J)

theorem chosenStarPoints_subset_ground {G : Finset (Finset α)} {r : α}
    (hr : r ∈ sources G) : chosenStarPoints G r ⊆ ground G := by
  intro x hx
  have hrG := (mem_sources.mp hr).1
  have hsG := mem_ground_of_forces hrG (starLeaf_spec hr).2
  change x ∈ ({r,starLeaf G r} : Finset α) at hx
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx
  exact hx.elim (fun e => e.symm ▸ hrG) (fun e => e.symm ▸ hsG)

theorem chosenStarPoints_disjoint_isolates {G : Finset (Finset α)} {r : α}
    (hr : r ∈ sources G) : Disjoint (chosenStarPoints G r) (isolated G) := by
  apply Finset.disjoint_left.mpr
  intro x hx hi
  have ⟨hrs,hrF⟩ := starLeaf_spec hr
  have hrG := (mem_sources.mp hr).1
  have hfL : starLeaf G r ∈ leaves G :=
    mem_leaves.mpr ⟨mem_ground_of_forces hrG hrF,r,hrG,hrs,hrF⟩
  change x ∈ ({r,starLeaf G r} : Finset α) at hx
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx
  rcases hx with he | he
  · exact (Finset.mem_sdiff.mp hi).2 (he.symm ▸ hr)
  · exact (mem_isolated.mp hi).2.2 (he.symm ▸ hfL)

theorem chosenStarPoints_disjoint_of_sources {G : Finset (Finset α)} {r a : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hr : r ∈ sources G) (ha : a ∈ sources G) (hra : r ≠ a) :
    Disjoint (chosenStarPoints G r) (chosenStarPoints G a) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  have hrNL := (Finset.mem_sdiff.mp (sources_subset_nonleaf hG hmin hr)).2
  have haNL := (Finset.mem_sdiff.mp (sources_subset_nonleaf hG hmin ha)).2
  have hrG := (mem_sources.mp hr).1
  have haG := (mem_sources.mp ha).1
  obtain ⟨hrs,hrF⟩ := starLeaf_spec hr
  obtain ⟨has,haF⟩ := starLeaf_spec ha
  have hrL : starLeaf G r ∈ leaves G :=
    mem_leaves.mpr ⟨mem_ground_of_forces hrG hrF,r,hrG,hrs,hrF⟩
  have haL : starLeaf G a ∈ leaves G :=
    mem_leaves.mpr ⟨mem_ground_of_forces haG haF,a,haG,has,haF⟩
  change x ∈ ({r,starLeaf G r} : Finset α) at hx
  change x ∈ ({a,starLeaf G a} : Finset α) at hy
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx hy
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact hra (hx.symm.trans hy)
  · exact hrNL (hy.symm.trans hx ▸ haL)
  · exact haNL (hx.symm.trans hy ▸ hrL)
  · have h := hx.symm.trans hy
    exact hra (weakMinimalGround_unique_proper_predecessor hG hmin hrG haG hrs
      (h.symm ▸ has) hrF (h.symm ▸ haF))

/-- Two known omissions and cardinality two identify the anchor block. -/
theorem omittedStars_eq_pair_of_card_two {G : Finset (Finset α)} {p q : α}
    (hp : p ∈ sources G) (hq : q ∈ sources G) (hpq : p ≠ q)
    (h2 : (omittedStars G (starPairMax G p q)).card = 2) :
    omittedStars G (starPairMax G p q) = {p,q} := by
  have hP := mem_omittedStars.mpr ⟨hp,starPairMax_omit_left G p q⟩
  have hQ := mem_omittedStars.mpr ⟨hq,starPairMax_omit_right G p q⟩
  have hS : ({p,q} : Finset α) ⊆ omittedStars G (starPairMax G p q) :=
    Finset.insert_subset_iff.mpr ⟨hP,Finset.singleton_subset_iff.mpr hQ⟩
  exact (Finset.eq_of_subset_of_card_le hS (by simp [h2,hpq])).symm

theorem omittedStars_eq_pair_of_allPairBlocks {G : Finset (Finset α)} {p q : α}
    (hp : p ∈ sources G) (hq : q ∈ sources G) (hpq : p ≠ q)
    (hAll : ∀ B ∈ starBlocks G, B.card = 2) :
    omittedStars G (starPairMax G p q) = {p,q} := by
  apply omittedStars_eq_pair_of_card_two hp hq hpq
  apply hAll
  exact Finset.mem_image_of_mem _ (starPairMax_mem hp hq hpq)

/-- With an ordinary omitted pair and unary anchors, the raw maximum
misses exactly the two chosen stars and its absent isolates. -/
theorem ground_sdiff_starPairMax_of_ordinary_pair
    {G : Finset (Finset α)} {p q : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hp : p ∈ sources G) (hq : q ∈ sources G) (hpq : p ≠ q)
    (hup : UnaryAtChosenLeaf G p) (huq : UnaryAtChosenLeaf G q)
    (hPair : omittedStars G (starPairMax G p q) = {p,q}) :
    ground G \ starPairMax G p q =
      (chosenStarPoints G p ∪ chosenStarPoints G q) ∪
        (isolated G \ starPairMax G p q) := by
  classical
  let T := starPairMax G p q
  obtain ⟨hps,hFp⟩ := starLeaf_spec hp
  obtain ⟨hqs,hFq⟩ := starLeaf_spec hq
  have hpN : p ∉ T := notMem_avoidBoth_top_of_forces (Or.inl hFp)
  have hqN : q ∉ T := notMem_avoidBoth_top_of_forces (Or.inr hFq)
  have hspN : starLeaf G p ∉ T := starPairMax_omit_left G p q
  have hsqN : starLeaf G q ∉ T := starPairMax_omit_right G p q
  have hT : T ∈ G := starPairMax_mem_family hG hmin hp hq hpq
  have hsource {r : α} (hr : r ∈ sources G) (hrp : r ≠ p) (hrq : r ≠ q) : r ∈ T := by
    have hOut : r ∈ sources G \ omittedStars G (starPairMax G p q) := by
      refine Finset.mem_sdiff.mpr ⟨hr,?_⟩
      rw [hPair]
      simp [hrp,hrq]
    have hrK : r ∈ ground (compressedStarPair G p q) := by
      rw [compressedStarPair_ground_eq_centers_union_present_isolates hG hmin hp hq hpq]
      exact Finset.mem_union_left _ hOut
    exact mem_raw_ground_of_mem_compress_ground hrK
  ext x
  constructor
  · intro hx
    obtain ⟨hxG,hxT⟩ := Finset.mem_sdiff.mp hx
    by_cases hxI : x ∈ isolated G
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hxI,hxT⟩)
    · apply Finset.mem_union_left _
      by_cases hxL : x ∈ leaves G
      · obtain ⟨r,hrG,hrx,hrxF⟩ := (mem_leaves.mp hxL).2
        have hrS : r ∈ sources G := mem_sources.mpr ⟨hrG,x,hrx,hrxF⟩
        by_cases erp : r = p
        · subst r
          have hxLeaf := hup hrx hrxF
          exact Finset.mem_union_left _ (Finset.mem_insert.mpr
            (Or.inr (Finset.mem_singleton.mpr hxLeaf)))
        · by_cases erq : r = q
          · subst r
            have hxLeaf := huq hrx hrxF
            exact Finset.mem_union_right _ (Finset.mem_insert.mpr
              (Or.inr (Finset.mem_singleton.mpr hxLeaf)))
          · exact False.elim (hxT (hrxF hT (hsource hrS erp erq)))
      · have hxS : x ∈ sources G := by
          by_contra hn
          exact hxI (Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨hxG,hxL⟩,hn⟩)
        by_cases exp : x = p
        · exact Finset.mem_union_left _ (Finset.mem_insert.mpr (Or.inl exp))
        · by_cases exq : x = q
          · exact Finset.mem_union_right _ (Finset.mem_insert.mpr (Or.inl exq))
          · exact False.elim (hxT (hsource hxS exp exq))
  · intro hx
    rcases Finset.mem_union.mp hx with hStars | hIso
    · rcases Finset.mem_union.mp hStars with hP | hQ
      · refine Finset.mem_sdiff.mpr ⟨chosenStarPoints_subset_ground hp hP,?_⟩
        change x ∈ ({p,starLeaf G p} : Finset α) at hP
        simp only [Finset.mem_insert,Finset.mem_singleton] at hP
        exact hP.elim (fun e => e.symm ▸ hpN) (fun e => e.symm ▸ hspN)
      · refine Finset.mem_sdiff.mpr ⟨chosenStarPoints_subset_ground hq hQ,?_⟩
        change x ∈ ({q,starLeaf G q} : Finset α) at hQ
        simp only [Finset.mem_insert,Finset.mem_singleton] at hQ
        exact hQ.elim (fun e => e.symm ▸ hqN) (fun e => e.symm ▸ hsqN)
    · obtain ⟨hi,hn⟩ := Finset.mem_sdiff.mp hIso
      exact Finset.mem_sdiff.mpr ⟨(mem_isolated.mp hi).1,hn⟩

theorem ground_sdiff_pairMax_sdiff_isolateOmission
    {G : Finset (Finset α)} {p q : α} {J : Finset α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hp : p ∈ sources G) (hq : q ∈ sources G) (hpq : p ≠ q)
    (hup : UnaryAtChosenLeaf G p) (huq : UnaryAtChosenLeaf G q)
    (hPair : omittedStars G (starPairMax G p q) = {p,q})
    (hJI : J ⊆ isolated G) :
    ground G \ (starPairMax G p q \ J) =
      (chosenStarPoints G p ∪ chosenStarPoints G q) ∪ pairIsolateHole G p q J := by
  have hJG : J ⊆ ground G := fun _ h => (mem_isolated.mp (hJI h)).1
  rw [Finset.sdiff_sdiff_eq_sdiff_union hJG,
    ground_sdiff_starPairMax_of_ordinary_pair hG hmin hp hq hpq hup huq hPair]
  simp only [pairIsolateHole,Finset.union_assoc]

private theorem intersect_pair_holes
    {G : Finset (Finset α)} {r a b : α} {M N : Finset α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (ha : a ∈ sources G) (hb : b ∈ sources G) (hab : a ≠ b)
    (hMI : M ⊆ isolated G) (hNI : N ⊆ isolated G) :
    ((chosenStarPoints G r ∪ chosenStarPoints G a) ∪ M) ∩
        ((chosenStarPoints G r ∪ chosenStarPoints G b) ∪ N) =
      chosenStarPoints G r ∪ (M ∩ N) := by
  have habD := Finset.disjoint_left.mp (chosenStarPoints_disjoint_of_sources hG hmin ha hb hab)
  have haI := Finset.disjoint_left.mp (chosenStarPoints_disjoint_isolates ha)
  have hbI := Finset.disjoint_left.mp (chosenStarPoints_disjoint_isolates hb)
  ext x
  simp only [Finset.mem_inter,Finset.mem_union]
  constructor
  · rintro ⟨hL,hR⟩
    rcases hL with (hr | ha') | hm <;> rcases hR with (hr' | hb') | hn
    · exact Or.inl hr
    · exact Or.inl hr
    · exact Or.inl hr
    · exact Or.inl hr'
    · exact False.elim (habD ha' hb')
    · exact False.elim (haI ha' (hNI hn))
    · exact Or.inl hr'
    · exact False.elim (hbI hb' (hMI hm))
    · exact Or.inr ⟨hm,hn⟩
  · rintro (hr | ⟨hm,hn⟩)
    · exact ⟨Or.inl (Or.inl hr),Or.inl (Or.inl hr)⟩
    · exact ⟨Or.inr hm,Or.inr hn⟩

/-- Union the two actual pair-fiber members with their relative isolate
omissions. Its omitted isolates are the intersection of the two
absolute isolate holes. The intersection may be empty; only a
nonempty intersection will count as an additional witness. -/
theorem mixedStarOmission_mem_of_two_ordinary_pair_omissions
    {G : Finset (Finset α)} {r a b : α} {J K : Finset α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hr : r ∈ sources G) (ha : a ∈ sources G) (hb : b ∈ sources G)
    (hra : r ≠ a) (hrb : r ≠ b) (hab : a ≠ b)
    (hur : UnaryAtChosenLeaf G r) (hua : UnaryAtChosenLeaf G a)
    (hub : UnaryAtChosenLeaf G b)
    (hPairA : omittedStars G (starPairMax G r a) = {r,a})
    (hPairB : omittedStars G (starPairMax G r b) = {r,b})
    (hJI : J ⊆ isolated G) (hKI : K ⊆ isolated G)
    (hJ : J ∈ starPairTrueComplement G r a)
    (hK : K ∈ starPairTrueComplement G r b) :
    mixedStarOmission G r (pairIsolateHole G r a J ∩ pairIsolateHole G r b K) ∈ G := by
  let A := starPairMax G r a \ J
  let B := starPairMax G r b \ K
  have hA : A ∈ G := (Finset.mem_filter.mp
    (raw_pairMax_sdiff_mem_of_isolate_atom_omission hG hmin hr ha hra hJI hJ)).1
  have hB : B ∈ G := (Finset.mem_filter.mp
    (raw_pairMax_sdiff_mem_of_isolate_atom_omission hG hmin hr hb hrb hKI hK)).1
  have hU := hG.2.2.1 hA hB
  have hHoleA : pairIsolateHole G r a J ⊆ isolated G :=
    Finset.union_subset Finset.sdiff_subset hJI
  have hHoleB : pairIsolateHole G r b K ⊆ isolated G :=
    Finset.union_subset Finset.sdiff_subset hKI
  have he : ground G \ (A ∪ B) =
      chosenStarPoints G r ∪ (pairIsolateHole G r a J ∩ pairIsolateHole G r b K) := by
    change ground G \ ((starPairMax G r a \ J) ∪ (starPairMax G r b \ K)) = _
    rw [Finset.sdiff_union_distrib,
      ground_sdiff_pairMax_sdiff_isolateOmission hG hmin hr ha hra hur hua hPairA hJI,
      ground_sdiff_pairMax_sdiff_isolateOmission hG hmin hr hb hrb hur hub hPairB hKI]
    exact intersect_pair_holes hG hmin ha hb hab hHoleA hHoleB
  have hEq : mixedStarOmission G r (pairIsolateHole G r a J ∩ pairIsolateHole G r b K) = A ∪ B := by
    unfold mixedStarOmission
    rw [←he,Finset.sdiff_sdiff_eq_self (subset_ground hU)]
  exact hEq.symm ▸ hU

#print axioms chosenStarPoints_disjoint_of_sources
#print axioms omittedStars_eq_pair_of_card_two
#print axioms omittedStars_eq_pair_of_allPairBlocks
#print axioms ground_sdiff_starPairMax_of_ordinary_pair
#print axioms mixedStarOmission_mem_of_two_ordinary_pair_omissions
end FranklForcingFiber

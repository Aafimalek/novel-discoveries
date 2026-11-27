import FranklStarIndex
import FranklPairExtra
import FranklPairSaturation
import FranklHeightThreeArithmetic

namespace FranklForcingFiber

variable {α : Type*} [DecidableEq α]

/-- The compressed-fiber bound without changing the original fiber's count. -/
theorem cross_pair_avoidance_upper {G : Finset (Finset α)} {p q s t : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hp : p ∈ ground G) (hq : q ∈ ground G) (hpq : p ≠ q)
    (hps : p ≠ s) (hqt : q ≠ t) (hf : Forces G p s) (hg : Forces G q t) :
    (avoidBoth G s t).card ≤ 1 + (pairReps G p q).card + (pairReps G p q).card.choose 2 := by
  rw [← cross_pair_compress_card hG hmin hp hq hpq hps hqt hf hg]
  exact FranklHeightThreeSauer.card_le (pairReps G p q)
    (compress_pair_unionClosed hG.2.2.1)
    (cross_pair_compress_noFourChain hG hmin hp hq hpq hps hqt hf hg
      (cross_pair_noFourChain hG hmin hp hq hpq hps hqt hf hg))
    (fun _ hA => compressPair_subset_reps hA)

/-- Once all pair maxima are full, any fixed pair of centers supplies
choose(k−2,2) additional distinct witnesses by omitting two other stars. -/
theorem extra_from_full_pair_maxima {G : Finset (Finset α)} {p q : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hp : p ∈ sources G) (hq : q ∈ sources G) (hpq : p ≠ q)
    (hfull : ∀ ⦃C⦄, C ⊆ sources G → C.card = 2 → outsideStars G C ∈ G) :
    (ground G).card + ((sources G).card - 2).choose 2 ≤
      (avoidBoth G (starLeaf G p) (starLeaf G q)).card + 1 := by
  let W := ((sources G).erase p).erase q
  let P := W.powersetCard 2
  let R := P.image (outsideStars G)
  have hW0 (C : Finset α) (hC : C ∈ P) : C ⊆ W := (Finset.mem_powersetCard.mp hC).1
  have hW1 : W ⊆ sources G := (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
  have hPsub (C : Finset α) (hC : C ∈ P) : C ⊆ sources G := (hW0 C hC).trans hW1
  have hRcard : R.card = ((sources G).card - 2).choose 2 := by
    have hinj : Set.InjOn (outsideStars G) (P : Set (Finset α)) :=
      fun a ha b hb he => outsideStars_inj hG hmin (hPsub a ha) (hPsub b hb) he
    dsimp [R]
    rw [Finset.card_image_of_injOn hinj, Finset.card_powersetCard]
    have hWp := Finset.card_erase_add_one hp
    have hWq := Finset.card_erase_add_one (Finset.mem_erase.mpr ⟨hpq.symm,hq⟩)
    change W.card + 1 = ((sources G).erase p).card at hWq
    have he : W.card = (sources G).card - 2 := by omega
    rw [he]
  have hR : ∀ ⦃A⦄, A ∈ R → A ∈ G ∧ starLeaf G p ∈ A ∧ starLeaf G q ∈ A ∧
      2 < ((ground G) \ A).card := by
    intro A hA
    obtain ⟨C,hC,rfl⟩ := Finset.mem_image.mp hA
    have hCS := hPsub C hC
    have hC2 := (Finset.mem_powersetCard.mp hC).2
    have hpC : p ∉ C := fun hh => (Finset.mem_erase.mp (Finset.mem_erase.mp (hW0 C hC hh)).2).1 rfl
    have hqC : q ∉ C := fun hh => (Finset.mem_erase.mp (hW0 C hC hh)).1 rfl
    refine ⟨hfull hCS hC2,repLeaf_mem_outsideStars hG hmin hCS hp hpC,
      repLeaf_mem_outsideStars hG hmin hCS hq hqC,?_⟩
    obtain ⟨a,b,hab,rfl⟩ := Finset.card_eq_two.mp hC2
    exact outsideStars_omit_more_than_two hG hmin hCS (by simp) (by simp) hab
  obtain ⟨hps,hFp⟩ := starLeaf_spec hp
  obtain ⟨hqt,hFq⟩ := starLeaf_spec hq
  obtain ⟨hs,ht,hts,_,hsT,htT⟩ := cross_pair_terminal_data hG hmin
    (mem_sources.mp hp).1 (mem_sources.mp hq).1 hpq hps hqt hFp hFq
  have e := terminal_pair_avoidance_extra hG hmin hs ht hts hsT htT hR
  rwa [hRcard] at e

theorem forcing_star_basic_count {G : Finset (Finset α)}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hk : 2 ≤ (sources G).card) :
    (ground G).card - 1 ≤ 1 + ((isolated G).card + (sources G).card - 2) +
      (((isolated G).card + (sources G).card - 2).choose 2) := by
  obtain ⟨p,hp,q,hq,hpq⟩ := Finset.one_lt_card.mp (by omega : 1 < (sources G).card)
  obtain ⟨hps,hFp⟩ := starLeaf_spec hp
  obtain ⟨hqt,hFq⟩ := starLeaf_spec hq
  have hpG := (mem_sources.mp hp).1
  have hqG := (mem_sources.mp hq).1
  obtain ⟨hs,ht,hts,_,hsT,htT⟩ := cross_pair_terminal_data hG hmin hpG hqG hpq hps hqt hFp hFq
  have hlo := terminal_pair_avoidance_card hG (weakMinimalGround_separated hG hmin) hs ht hts hsT htT
  have hhi := cross_pair_avoidance_upper hG hmin hpG hqG hpq hps hqt hFp hFq
  rw [pairReps_card_formula hG hmin hp hq hpq] at hhi
  omega

/-- When the reduced support cannot lose a representative, every set formed
by removing exactly two complete stars is an original member. -/
theorem all_pair_maxima_full {G : Finset (Finset α)}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hLarge : let m := (isolated G).card + (sources G).card - 2
      1 + (m-1) + (m-1).choose 2 < (ground G).card - 1) :
    ∀ ⦃C⦄, C ⊆ sources G → C.card = 2 → outsideStars G C ∈ G := by
  classical
  intro C hC h2
  obtain ⟨a,b,hab,rfl⟩ := Finset.card_eq_two.mp h2
  have ha : a ∈ sources G := hC (by simp)
  have hb : b ∈ sources G := hC (by simp)
  have haG := (mem_sources.mp ha).1
  have hbG := (mem_sources.mp hb).1
  obtain ⟨has, hFas⟩ := starLeaf_spec ha
  obtain ⟨hbt, hFbt⟩ := starLeaf_spec hb
  obtain ⟨hs,ht,hts,_,hsT,htT⟩ := cross_pair_terminal_data hG hmin haG hbG hab has hbt hFas hFbt
  have hl := terminal_pair_avoidance_card hG (weakMinimalGround_separated hG hmin) hs ht hts hsT htT
  have hc := Finset.card_erase_add_one hs
  have hd := Finset.card_erase_add_one (Finset.mem_erase.mpr ⟨hts,ht⟩)
  have hn : (avoidBoth G (starLeaf G a) (starLeaf G b)).Nonempty :=
    Finset.card_pos.mp (by omega)
  have hlarge' : 1 + ((pairReps G a b).card - 1) + ((pairReps G a b).card - 1).choose 2 <
      (ground G).card - 1 := by
    rw [pairReps_card_formula hG hmin ha hb hab]
    exact hLarge
  have hEq : outsideStars G {a,b} = ground (avoidBoth G (starLeaf G a) (starLeaf G b)) := by
    ext x
    rw [cross_pair_top_exact_of_ground_bound hG hmin haG hbG hab has hbt hFas hFbt hlarge']
    simp only [mem_outsideStars, Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]
    constructor
    · rintro ⟨hxG,hxA,hxB⟩
      exact ⟨hxG,fun e => hxA (e.symm ▸ forces_refl G a),
        fun e => hxB (e.symm ▸ forces_refl G b),hxA,hxB⟩
    · rintro ⟨hxG,_,_,hxA,hxB⟩
      exact ⟨hxG,hxA,hxB⟩
  rw [hEq]
  exact avoidBoth_top_mem hG hn

/-- Either a cross-star pair fiber can lose a representative, or all full
pair maxima from the other stars contribute extra distinct members. -/
theorem forcing_star_count_disjunction {G : Finset (Finset α)}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hk : 2 ≤ (sources G).card) :
    let m := (isolated G).card + (sources G).card - 2
    (ground G).card - 1 ≤ 1 + (m-1) + (m-1).choose 2 ∨
      (ground G).card - 1 + ((sources G).card - 2).choose 2 ≤ 1 + m + m.choose 2 := by
  let m := (isolated G).card + (sources G).card - 2
  change (ground G).card - 1 ≤ 1 + (m-1) + (m-1).choose 2 ∨
    (ground G).card - 1 + ((sources G).card - 2).choose 2 ≤ 1 + m + m.choose 2
  by_cases h : (ground G).card - 1 ≤ 1 + (m-1) + (m-1).choose 2
  · exact Or.inl h
  · have hfull := all_pair_maxima_full hG hmin (Nat.lt_of_not_ge h)
    obtain ⟨p,hp,q,hq,hpq⟩ := Finset.one_lt_card.mp (by omega : 1 < (sources G).card)
    obtain ⟨hps,hFp⟩ := starLeaf_spec hp
    obtain ⟨hqt,hFq⟩ := starLeaf_spec hq
    have hlo := extra_from_full_pair_maxima hG hmin hp hq hpq hfull
    have hhi := cross_pair_avoidance_upper hG hmin (mem_sources.mp hp).1 (mem_sources.mp hq).1 hpq hps hqt hFp hFq
    rw [pairReps_card_formula hG hmin hp hq hpq] at hhi
    change (avoidBoth G (starLeaf G p) (starLeaf G q)).card ≤ 1+m+m.choose 2 at hhi
    exact Or.inr (by omega)

theorem forcing_star_leaf_bound {G : Finset (Finset α)}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G) (hk : 2 ≤ (sources G).card) :
    (leaves G).card ≤ ((isolated G).card + (sources G).card - 2).choose 2 :=
  FranklHeightThreeArithmetic.tail_le_choose_of_basic (partition_card hG hmin)
    rfl hk (forcing_star_basic_count hG hmin hk)

/-- In a weak ground-minimal counterexample with no isolated ground points
and at least two stars, there are at least eight centers. Exactly eight
centers permit eight or nine leaves. The one-star case is not covered. -/
theorem no_isolated_forcing_star_count {G : Finset (Finset α)}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hi : (isolated G).card = 0) (hk : 2 ≤ (sources G).card) :
    8 ≤ (sources G).card ∧ ((sources G).card = 8 → 8 ≤ (leaves G).card ∧ (leaves G).card ≤ 9) := by
  have hn := partition_card hG hmin
  have hL := sources_card_le_leaves hG hmin
  have hb := forcing_star_leaf_bound hG hmin hk
  rw [hi,zero_add] at hn hb
  have hk3 : 1 ≤ (sources G).card - 2 := by
    by_contra! h
    have h2 : (sources G).card - 2 = 0 := by omega
    rw [h2, Nat.choose_zero_succ] at hb
    omega
  have h := forcing_star_count_disjunction hG hmin hk
  dsimp only at h
  rw [hi,zero_add] at h
  exact FranklHeightThreeArithmetic.no_isolates_side_bounds hn rfl hk hk3 hL h

theorem forcing_star_leaf_strict_bound {G : Finset (Finset α)}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hk : 4 ≤ (sources G).card) :
    (leaves G).card < ((isolated G).card + (sources G).card - 2).choose 2 :=
  FranklHeightThreeArithmetic.tail_lt_choose_of_strengthened (partition_card hG hmin)
    rfl hk (forcing_star_count_disjunction hG hmin (by omega))

/-- The disjunction also gives an explicit slack in the binomial bound. -/
theorem forcing_star_leaf_slack {G : Finset (Finset α)}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G) (hk : 2 ≤ (sources G).card)
    (hm : 1 ≤ (isolated G).card + (sources G).card - 2) :
    let m := (isolated G).card + (sources G).card - 2
    (leaves G).card + min m (((sources G).card - 2).choose 2) ≤ m.choose 2 :=
  FranklHeightThreeArithmetic.tail_add_min_le_choose_of_strengthened (partition_card hG hmin)
    rfl hk hm (forcing_star_count_disjunction hG hmin hk)

#print axioms forcing_star_leaf_slack
#print axioms all_pair_maxima_full
#print axioms forcing_star_count_disjunction
#print axioms forcing_star_leaf_bound
#print axioms no_isolated_forcing_star_count
#print axioms forcing_star_leaf_strict_bound
#print axioms extra_from_full_pair_maxima
#print axioms forcing_star_basic_count

end FranklForcingFiber

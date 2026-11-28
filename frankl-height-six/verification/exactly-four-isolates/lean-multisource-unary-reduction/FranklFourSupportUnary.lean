import FranklMultiLeafPair

/- Kernel-checked on pinned Lean 4.36 and Mathlib. -/
namespace FranklForcingFiber

variable {α : Type*} [DecidableEq α]

/-- A pair cannot itself be a member in the no-empty, no-strict-majority
setting. Adjoining the pair injects neither into both, missing the pair. -/
theorem weak_no_pair_member {G : Finset (Finset α)} (hG : NoStrictMajority G)
    (y z : α) : ({y,z} : Finset α) ∉ G := by
  classical
  intro hp
  let R : Finset α := {y,z}
  let E := G.filter (fun A => ¬ (y ∈ A ∨ z ∈ A))
  let C := G.filter (fun A => y ∈ A ∧ z ∈ A)
  have hCE : C.card ≤ E.card := both_count_le_neither_count
    (hG.2.2.2.2 y) (hG.2.2.2.2 z)
  have hRC : R ∈ C := Finset.mem_filter.mpr ⟨hp,by simp [R],by simp [R]⟩
  have hmap : Set.MapsTo (fun A : Finset α => A ∪ R) (E : Set (Finset α))
      (C.erase R : Set (Finset α)) := by
    intro A ha
    have ha' : A ∈ E := ha
    obtain ⟨haG,haN⟩ := Finset.mem_filter.mp ha'
    refine Finset.mem_erase.mpr ⟨?_,Finset.mem_filter.mpr
      ⟨hG.2.2.1 haG hp,by simp [R],by simp [R]⟩⟩
    intro he
    obtain ⟨w,hw⟩ := hG.2.1 haG
    have hwR : w ∈ R := he ▸ Finset.mem_union_left R hw
    simp only [R,Finset.mem_insert,Finset.mem_singleton] at hwR
    rcases hwR with rfl | rfl
    · exact haN (Or.inl hw)
    · exact haN (Or.inr hw)
  have hInj : Set.InjOn (fun A : Finset α => A ∪ R) (E : Set (Finset α)) := by
    intro A ha D hd he
    have ha' : A ∈ E := ha
    have hd' : D ∈ E := hd
    have hclean : ∀ ⦃T⦄, T ∈ E → (T ∪ R) \ R = T := by
      intro T ht
      have htn := (Finset.mem_filter.mp ht).2
      ext w
      constructor
      · intro hw
        obtain ⟨hwU,hwR⟩ := Finset.mem_sdiff.mp hw
        exact (Finset.mem_union.mp hwU).elim id (fun hh => False.elim (hwR hh))
      · intro hw
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_union_left R hw,?_⟩
        intro hwR
        simp only [R,Finset.mem_insert,Finset.mem_singleton] at hwR
        rcases hwR with rfl | rfl
        · exact htn (Or.inl hw)
        · exact htn (Or.inr hw)
    have hEq := congrArg (fun T : Finset α => T \ R) he
    simpa only [hclean ha', hclean hd'] using hEq
  have hE := Finset.card_le_card_of_injOn (fun A : Finset α => A ∪ R) hmap hInj
  have hC := Finset.card_erase_add_one hRC
  omega

/-- Weak no-majority families of nonempty sets have no sets of size 1 or 2. -/
theorem weak_member_card_ge_three {G : Finset (Finset α)} {A : Finset α}
    (hG : NoStrictMajority G) (hA : A ∈ G) : 3 ≤ A.card := by
  have hP : 0 < A.card := Finset.card_pos.mpr (hG.2.1 hA)
  by_contra hn
  by_cases hc : A.card = 1
  · obtain ⟨x,rfl⟩ := Finset.card_eq_one.mp hc
    exact weak_no_singleton hG x hA
  · have hc2 : A.card = 2 := by omega
    obtain ⟨x,y,_,rfl⟩ := Finset.card_eq_two.mp hc2
    exact weak_no_pair_member hG x y hA

/-- At most five original members fit inside any four-point support,
by injecting them into empty or singleton complements in the support. -/
theorem weak_four_support_card_le_five {G E : Finset (Finset α)} {U : Finset α}
    (hG : NoStrictMajority G) (hEU : E ⊆ G) (hU : U.card ≤ 4)
    (hS : ∀ ⦃A⦄, A ∈ E → A ⊆ U) : E.card ≤ 5 := by
  classical
  let W := insert (∅ : Finset α) (U.image fun x => ({x} : Finset α))
  let f := fun A : Finset α => U \ A
  have hmaps : Set.MapsTo f (E : Set (Finset α)) (W : Set (Finset α)) := by
    intro A ha
    have hAE : A ∈ E := ha
    have hc := Finset.card_sdiff_add_card_eq_card (hS hAE)
    have h3 := weak_member_card_ge_three hG (hEU hAE)
    have hcf : (f A).card ≤ 1 := by
      change (U \ A).card ≤ 1
      omega
    by_cases he0 : (f A).card = 0
    · have he := Finset.card_eq_zero.mp he0
      exact Finset.mem_insert.mpr (Or.inl he)
    · have he1 : (f A).card = 1 := by omega
      obtain ⟨x,he⟩ := Finset.card_eq_one.mp he1
      have hx : x ∈ U := by
        have hxf : x ∈ f A := he.symm ▸ Finset.mem_singleton_self x
        exact (Finset.mem_sdiff.mp hxf).1
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_image.mpr ⟨x,hx,he.symm⟩))
  have hinj : Set.InjOn f (E : Set (Finset α)) := by
    intro A ha B hb he
    have hAE : A ∈ E := ha
    have hBE : B ∈ E := hb
    have hclean {T : Finset α} (hT : T ⊆ U) : U \ f T = T :=
      Finset.sdiff_sdiff_eq_self hT
    have h' := congrArg (fun T : Finset α => U \ T) he
    simpa only [hclean (hS hAE),hclean (hS hBE)] using h'
  have hW : W.card ≤ U.card + 1 := by
    exact (Finset.card_insert_le _ _).trans
      (Nat.add_le_add_right Finset.card_image_le 1)
  have h := Finset.card_le_card_of_injOn f hmaps hinj
  omega

/-- Exactly four isolates and a second source prohibit any
multileaf anchor. This uses no general small-ground theorem. -/
theorem exact_four_no_multileaf_anchored_pair
    {G : Finset (Finset α)} {p q s t u : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hI : (isolated G).card = 4)
    (hp : p ∈ ground G) (hq : q ∈ ground G) (hpq : p ≠ q)
    (hps : p ≠ s) (hqt : q ≠ t) (hpu : p ≠ u) (hus : u ≠ s)
    (hFp : Forces G p s) (hFq : Forces G q t) (hFu : Forces G p u) : False := by
  obtain ⟨hs,ht,hts,_,hsT,htT⟩ :=
    cross_pair_terminal_data hG hmin hp hq hpq hps hqt hFp hFq
  have hbase := terminal_pair_avoidance_card hG (weakMinimalGround_separated hG hmin)
    hs ht hts hsT htT
  have hcapSupport := cross_pair_top_subset_isolated_of_multileaf hG hmin hp hq hpq
    hps hqt hpu hus hFp hFq hFu
  have hsubG : avoidBoth G s t ⊆ G := Finset.filter_subset _ _
  have hcap := weak_four_support_card_le_five hG hsubG hI.le
    (fun _ hA => (subset_ground hA).trans hcapSupport)
  have hk : 1 < (sources G).card := Finset.one_lt_card_iff.mpr
    ⟨p,q,mem_sources.mpr ⟨hp,s,hps,hFp⟩,mem_sources.mpr ⟨hq,t,hqt,hFq⟩,hpq⟩
  have hL := sources_card_le_leaves hG hmin
  have hpart := partition_card hG hmin
  omega

/-- In the multiple-source four-isolate case every source has exactly
one proper forcing successor, since source membership supplies at least one. -/
theorem exact_four_proper_forcing_successor_unique
    {G : Finset (Finset α)} {p s u : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hI : (isolated G).card = 4) (hk : 2 ≤ (sources G).card)
    (hp : p ∈ sources G) (hps : p ≠ s) (hpu : p ≠ u)
    (hFs : Forces G p s) (hFu : Forces G p u) : s = u := by
  by_contra hsu
  have hc := Finset.card_erase_add_one hp
  have hQ : ((sources G).erase p).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨q,hq⟩ := hQ
  obtain ⟨hqp,hqS⟩ := Finset.mem_erase.mp hq
  obtain ⟨hqt,hFt⟩ := starLeaf_spec hqS
  exact exact_four_no_multileaf_anchored_pair hG hmin hI (mem_sources.mp hp).1
    (mem_sources.mp hqS).1 hqp.symm hps hqt hpu (fun e => hsu e.symm) hFs hFt hFu

#print axioms weak_no_pair_member
#print axioms weak_member_card_ge_three
#print axioms weak_four_support_card_le_five
#print axioms exact_four_no_multileaf_anchored_pair
#print axioms exact_four_proper_forcing_successor_unique
end FranklForcingFiber

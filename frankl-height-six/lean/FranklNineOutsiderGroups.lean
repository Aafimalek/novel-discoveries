import FranklExcludeTwelveStars

open scoped BigOperators
namespace FranklBlockIncidence
variable {α : Type*} [DecidableEq α]

private theorem card_groups_add_links_ge_nine {S : Finset α} {B : Finset (Finset α)}
    {A : Finset α} {b : α} (hD : PairDesign S B) (hA : A ∈ B) (hb : b ∈ A)
    (hE : (S \ A).card = 9) :
    9 ≤ (groupsThrough B A b).card + (groupLinks B A b).card := by
  classical
  let M := groupsThrough B A b
  have hM {T : Finset α} (hT : T ∈ M) : T ≠ A ∧ T ∈ B ∧ b ∈ T := by
    obtain ⟨hTe,hbT⟩ := Finset.mem_filter.mp hT
    obtain ⟨hne,hTB⟩ := Finset.mem_erase.mp hTe
    exact ⟨hne,hTB,hbT⟩
  have hCover : M.biUnion (fun T => T \ A) = S \ A := by
    ext x
    constructor
    · intro hx
      obtain ⟨T,hT,hxT⟩ := Finset.mem_biUnion.mp hx
      obtain ⟨hx,hnot⟩ := Finset.mem_sdiff.mp hxT
      exact Finset.mem_sdiff.mpr ⟨(hD.1 T (hM hT).2.1).1 hx,hnot⟩
    · intro hx
      obtain ⟨hxS,hnot⟩ := Finset.mem_sdiff.mp hx
      have hbn : b ≠ x := fun e => hnot (e ▸ hb)
      obtain ⟨T,⟨hTB,hbT,hxT⟩,_⟩ := hD.2 b ((hD.1 A hA).1 hb) x hxS hbn
      have hneq : T ≠ A := fun e => hnot (e ▸ hxT)
      exact Finset.mem_biUnion.mpr ⟨T,Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hneq,hTB⟩,hbT⟩,
        Finset.mem_sdiff.mpr ⟨hxT,hnot⟩⟩
  have hDisj : (M : Set (Finset α)).PairwiseDisjoint (fun T => T \ A) := by
    intro T hT V hV hne
    apply Finset.disjoint_left.mpr
    intro x hxT hxV
    obtain ⟨_,hTB,hbT⟩ := hM hT
    obtain ⟨_,hVB,hbV⟩ := hM hV
    obtain ⟨hxT',hxA⟩ := Finset.mem_sdiff.mp hxT
    exact hne (blocks_eq_of_common_pair hD hTB hVB hbT hxT' hbV (Finset.mem_sdiff.mp hxV).1
      (fun e => hxA (e ▸ hb)))
  have hDisj2 : (M : Set (Finset α)).PairwiseDisjoint (fun T => (T \ A).powersetCard 2) := by
    intro T hT V hV hne
    apply Finset.disjoint_left.mpr
    intro e heT heV
    obtain ⟨heT',h2⟩ := Finset.mem_powersetCard.mp heT
    obtain ⟨heV',_⟩ := Finset.mem_powersetCard.mp heV
    obtain ⟨x,hx⟩ := Finset.card_pos.mp (show 0 < e.card by omega)
    exact Finset.disjoint_left.mp (hDisj hT hV hne) (heT' hx) (heV' hx)
  have hsum := Finset.card_biUnion hDisj
  rw [hCover,hE] at hsum
  have hsum' := Finset.card_biUnion hDisj2
  change (groupLinks B A b).card = _ at hsum'
  simp only [Finset.card_powersetCard] at hsum'
  have hu : ∑ T ∈ M, (T \ A).card ≤ ∑ T ∈ M, (1 + (T \ A).card.choose 2) := by
    apply Finset.sum_le_sum
    intro T hT
    have hc : (T \ A).card ≤ 9 := by
      rw [← hE]
      apply Finset.card_le_card
      intro x hx
      obtain ⟨hxt,hxA⟩ := Finset.mem_sdiff.mp hx
      exact Finset.mem_sdiff.mpr ⟨(hD.1 T (hM hT).2.1).1 hxt,hxA⟩
    generalize hn : (T \ A).card = d at hc ⊢
    interval_cases d <;> decide
  change 9 ≤ M.card + (groupLinks B A b).card
  rw [Finset.sum_add_distrib,← Finset.card_eq_sum_ones,← hsum',← hsum] at hu
  exact hu

private theorem groupLinks_subset_blockLinks {S : Finset α} {B : Finset (Finset α)}
    {A : Finset α} {b : α} (hD : PairDesign S B) (hb : b ∈ A) :
    groupLinks B A b ⊆ blockLinks S B A := by
  intro e he
  obtain ⟨T,hT,heT⟩ := Finset.mem_biUnion.mp he
  obtain ⟨heT',he2⟩ := Finset.mem_powersetCard.mp heT
  obtain ⟨hTe,hbT⟩ := Finset.mem_filter.mp hT
  have hTB := (Finset.mem_erase.mp hTe).2
  apply mem_blockLinks.mpr
  refine ⟨?_,he2,T,hTB,heT'.trans Finset.sdiff_subset,⟨b,Finset.mem_inter.mpr ⟨hb,hbT⟩⟩⟩
  intro x hx
  obtain ⟨hxT,hxA⟩ := Finset.mem_sdiff.mp (heT' hx)
  exact Finset.mem_sdiff.mpr ⟨(hD.1 T hTB).1 hxT,hxA⟩

private theorem disjoint_groupLinks {S : Finset α} {B : Finset (Finset α)} {A : Finset α}
    {b c : α} (hD : PairDesign S B) (hA : A ∈ B) (hb : b ∈ A) (hc : c ∈ A) (hbc : b ≠ c) :
    Disjoint (groupLinks B A b) (groupLinks B A c) := by
  apply Finset.disjoint_left.mpr
  intro e he1 he2
  obtain ⟨T,hT,hEt⟩ := Finset.mem_biUnion.mp he1
  obtain ⟨V,hV,hEv⟩ := Finset.mem_biUnion.mp he2
  obtain ⟨hEt',he2⟩ := Finset.mem_powersetCard.mp hEt
  obtain ⟨hEv',_⟩ := Finset.mem_powersetCard.mp hEv
  obtain ⟨x,y,hxy,rfl⟩ := Finset.card_eq_two.mp he2
  obtain ⟨hTe,hbT⟩ := Finset.mem_filter.mp hT
  obtain ⟨hVe,hcV⟩ := Finset.mem_filter.mp hV
  obtain ⟨hTn,hTB⟩ := Finset.mem_erase.mp hTe
  have hVB := (Finset.mem_erase.mp hVe).2
  have he := blocks_eq_of_common_pair hD hTB hVB
    (Finset.mem_sdiff.mp (hEt' (by simp))).1 (Finset.mem_sdiff.mp (hEt' (by simp))).1
    (Finset.mem_sdiff.mp (hEv' (by simp))).1 (Finset.mem_sdiff.mp (hEv' (by simp))).1 hxy
  exact hTn (blocks_eq_of_common_pair hD hTB hA hbT (he.symm ▸ hcV) hb hc hbc)

noncomputable def outsideBlocks (B : Finset (Finset α)) (A : Finset α) : Finset (Finset α) := by
  classical
  exact B.filter (Disjoint A)

theorem mem_outsideBlocks {B : Finset (Finset α)} {A T : Finset α} :
    T ∈ outsideBlocks B A ↔ T ∈ B ∧ Disjoint A T := by
  classical
  exact Finset.mem_filter

theorem five_outside_blocks_of_nine_ten {S : Finset α} {B : Finset (Finset α)}
    {A : Finset α} (hD : PairDesign S B) (hr : ∀ C ∈ B, C.card ≤ 4)
    (h9 : (S \ A).card = 9) (h10 : (blockLinks S B A).card ≤ 10) :
    5 ≤ (outsideBlocks B A).card := by
  classical
  let D := outsideBlocks B A
  let E := S \ A
  let L := blockLinks S B A
  let M := D.biUnion (fun C => C.powersetCard 2)
  have hcover : E.powersetCard 2 ⊆ L ∪ M := by
    intro e he
    obtain ⟨heE,he2⟩ := Finset.mem_powersetCard.mp he
    obtain ⟨u,v,huv,heEq⟩ := Finset.card_eq_two.mp he2
    have hu : u ∈ e := heEq.symm ▸ Finset.mem_insert_self _ _
    have hv : v ∈ e := heEq.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self v)
    have huS := (Finset.mem_sdiff.mp (heE hu)).1
    have hvS := (Finset.mem_sdiff.mp (heE hv)).1
    obtain ⟨T,⟨hTB,huT,hvT⟩,_⟩ := hD.2 u huS v hvS huv
    have hsub : e ⊆ T := by
      rw [heEq]
      exact Finset.insert_subset_iff.mpr ⟨huT,Finset.singleton_subset_iff.mpr hvT⟩
    by_cases hd : Disjoint A T
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr
        ⟨T,mem_outsideBlocks.mpr ⟨hTB,hd⟩,Finset.mem_powersetCard.mpr ⟨hsub,he2⟩⟩))
    · have hn : (A ∩ T).Nonempty := by
        by_contra hn
        exact hd (Finset.disjoint_left.mpr (fun x hx hy => hn ⟨x,Finset.mem_inter.mpr ⟨hx,hy⟩⟩))
      exact Finset.mem_union.mpr (Or.inl (mem_blockLinks.mpr ⟨heE,he2,T,hTB,hsub,hn⟩))
  have hM : M.card ≤ D.card * 6 := by
    calc
      M.card ≤ ∑ C ∈ D, (C.powersetCard 2).card := Finset.card_biUnion_le
      _ ≤ ∑ _C ∈ D, 6 := by
        apply Finset.sum_le_sum
        intro C hC
        rw [Finset.card_powersetCard]
        exact (Nat.choose_le_choose 2 (hr C (mem_outsideBlocks.mp hC).1)).trans (by decide)
      _ = D.card*6 := by simp
  have hcap := Finset.card_le_card hcover
  change E.card = 9 at h9
  rw [Finset.card_powersetCard,h9] at hcap
  change 36 ≤ (L ∪ M).card at hcap
  change L.card ≤ 10 at h10
  have hsum := Finset.card_union_le L M
  change 5 ≤ D.card
  omega

/-- A four-block with nine outsiders and at most ten links has some
pair with at least eighteen blocks avoiding that pair. -/
theorem some_away_card_ge_eighteen_of_four_block_nine_ten
    {S : Finset α} {B : Finset (Finset α)} {A : Finset α}
    (hD : PairDesign S B) (hr : ∀ C ∈ B, C.card ≤ 4) (hA : A ∈ B) (h4 : A.card = 4)
    (h9 : (S \ A).card = 9) (h10 : (blockLinks S B A).card ≤ 10) :
    ∃ p ∈ A, ∃ q ∈ A, p ≠ q ∧ 18 ≤ (away B p q).card := by
  classical
  have hDisj : (A : Set α).PairwiseDisjoint (groupLinks B A) := by
    intro b hb c hc hbc
    exact disjoint_groupLinks hD hA hb hc hbc
  have hsub : A.biUnion (groupLinks B A) ⊆ blockLinks S B A := by
    intro e he
    obtain ⟨b,hb,heB⟩ := Finset.mem_biUnion.mp he
    exact groupLinks_subset_blockLinks hD hb heB
  have hsum := Finset.card_le_card hsub
  rw [Finset.card_biUnion hDisj] at hsum
  have hsum10 : (∑ b ∈ A, (groupLinks B A b).card) ≤ 10 := hsum.trans h10
  have haux {p q b c : α} (hp : p ∈ A) (hq : q ∈ A) (hb : b ∈ A) (hc : c ∈ A)
      (hbp : b ≠ p) (hbq : b ≠ q) (hcp : c ≠ p) (hcq : c ≠ q) (hbc : b ≠ c)
      (h5 : (groupLinks B A b).card + (groupLinks B A c).card ≤ 5) :
      18 ≤ (away B p q).card := by
    let P := groupsThrough B A b
    let Q := groupsThrough B A c
    let D := outsideBlocks B A
    have g₁ := card_groups_add_links_ge_nine hD hA hb h9
    have g₂ := card_groups_add_links_ge_nine hD hA hc h9
    change 9 ≤ P.card + (groupLinks B A b).card at g₁
    change 9 ≤ Q.card + (groupLinks B A c).card at g₂
    have hd5 : 5 ≤ D.card := five_outside_blocks_of_nine_ten hD hr h9 h10
    have haway {z : α} (hz : z ∈ A) (hzp : z ≠ p) (hzq : z ≠ q) :
        groupsThrough B A z ⊆ away B p q := by
      intro C hC
      obtain ⟨hCe,hzC⟩ := Finset.mem_filter.mp hC
      obtain ⟨hCne,hCB⟩ := Finset.mem_erase.mp hCe
      exact mem_away.mpr ⟨hCB,
        fun h => hCne (blocks_eq_of_common_pair hD hCB hA hzC h hz hp hzp),
        fun h => hCne (blocks_eq_of_common_pair hD hCB hA hzC h hz hq hzq)⟩
    have hdP : Disjoint P Q := by
      apply Finset.disjoint_left.mpr
      intro C hCP hCQ
      obtain ⟨hCe,hbC⟩ := Finset.mem_filter.mp hCP
      obtain ⟨hCne,hCB⟩ := Finset.mem_erase.mp hCe
      exact hCne (blocks_eq_of_common_pair hD hCB hA hbC (Finset.mem_filter.mp hCQ).2 hb hc hbc)
    have hdD : Disjoint (P ∪ Q) D := by
      apply Finset.disjoint_left.mpr
      intro C hCU hCD
      have hd := (mem_outsideBlocks.mp hCD).2
      exact (Finset.mem_union.mp hCU).elim
        (fun h => Finset.disjoint_left.mp hd hb (Finset.mem_filter.mp h).2)
        (fun h => Finset.disjoint_left.mp hd hc (Finset.mem_filter.mp h).2)
    have hDaway : D ⊆ away B p q := by
      intro C hC
      obtain ⟨hCB,hCD⟩ := mem_outsideBlocks.mp hC
      exact mem_away.mpr ⟨hCB,Finset.disjoint_left.mp hCD hp,Finset.disjoint_left.mp hCD hq⟩
    have he := Finset.card_le_card (Finset.union_subset
      (Finset.union_subset (haway hb hbp hbq) (haway hc hcp hcq)) hDaway)
    rw [Finset.card_union_of_disjoint hdD,Finset.card_union_of_disjoint hdP] at he
    omega
  obtain ⟨p,q,b,c,hpq,hpb,hpc,hqb,hqc,hbc,hEq⟩ := Finset.card_eq_four.mp h4
  have hp : p ∈ A := hEq.symm ▸ (show p ∈ ({p,q,b,c} : Finset α) by simp)
  have hq : q ∈ A := hEq.symm ▸ (show q ∈ ({p,q,b,c} : Finset α) by simp)
  have hb : b ∈ A := hEq.symm ▸ (show b ∈ ({p,q,b,c} : Finset α) by simp)
  have hc : c ∈ A := hEq.symm ▸ (show c ∈ ({p,q,b,c} : Finset α) by simp)
  have hsum' : (∑ z ∈ ({p,q,b,c} : Finset α), (groupLinks B A z).card) ≤ 10 := by
    rw [← hEq]
    exact hsum10
  simp [Finset.sum_insert,hpq,hpb,hpc,hqb,hqc,hbc] at hsum'
  by_cases h5 : (groupLinks B A b).card + (groupLinks B A c).card ≤ 5
  · exact ⟨p,hp,q,hq,hpq,haux hp hq hb hc hpb.symm hqb.symm hpc.symm hqc.symm hbc h5⟩
  · have h5' : (groupLinks B A p).card + (groupLinks B A q).card ≤ 5 := by omega
    exact ⟨b,hb,c,hc,hbc,haux hb hc hp hq hpb hpc hqb hqc hpq h5'⟩

#print axioms five_outside_blocks_of_nine_ten
#print axioms some_away_card_ge_eighteen_of_four_block_nine_ten
end FranklBlockIncidence

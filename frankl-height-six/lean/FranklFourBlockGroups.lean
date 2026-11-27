import FranklBlockClosureEncoding

open scoped BigOperators
namespace FranklBlockIncidence
variable {α : Type*} [DecidableEq α]

omit [DecidableEq α] in
theorem blocks_eq_of_common_pair {S : Finset α} {B : Finset (Finset α)}
    {K L : Finset α} {x y : α} (hD : PairDesign S B)
    (hK : K ∈ B) (hL : L ∈ B) (hxK : x ∈ K) (hyK : y ∈ K)
    (hxL : x ∈ L) (hyL : y ∈ L) (hxy : x ≠ y) : K = L := by
  obtain ⟨_,_,hU⟩ := hD.2 x ((hD.1 K hK).1 hxK) y ((hD.1 K hK).1 hyK) hxy
  exact (hU K ⟨hK,hxK,hyK⟩).trans (hU L ⟨hL,hxL,hyL⟩).symm

def groupsThrough (B : Finset (Finset α)) (A : Finset α) (b : α) : Finset (Finset α) :=
  (B.erase A).filter (b ∈ ·)

def groupLinks (B : Finset (Finset α)) (A : Finset α) (b : α) : Finset (Finset α) :=
  (groupsThrough B A b).biUnion (fun T => (T \ A).powersetCard 2)

private theorem card_groups_add_links_ge_eight {S : Finset α} {B : Finset (Finset α)}
    {A : Finset α} {b : α} (hD : PairDesign S B) (hA : A ∈ B) (hb : b ∈ A)
    (hE : (S \ A).card = 8) :
    8 ≤ (groupsThrough B A b).card + (groupLinks B A b).card := by
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
    have hc : (T \ A).card ≤ 8 := by
      rw [← hE]
      apply Finset.card_le_card
      intro x hx
      obtain ⟨hxt,hxA⟩ := Finset.mem_sdiff.mp hx
      exact Finset.mem_sdiff.mpr ⟨(hD.1 T (hM hT).2.1).1 hxt,hxA⟩
    generalize hn : (T \ A).card = d at hc ⊢
    interval_cases d <;> decide
  change 8 ≤ M.card + (groupLinks B A b).card
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

private theorem exists_block_disjoint_of_eight_six {S : Finset α} {B : Finset (Finset α)}
    {A : Finset α} (hD : PairDesign S B) (h8 : (S \ A).card = 8)
    (h6 : (blockLinks S B A).card ≤ 6) :
    ∃ T ∈ B, Disjoint A T := by
  classical
  by_contra hn
  have hsub : (S \ A).powersetCard 2 ⊆ blockLinks S B A := by
    intro e hE
    obtain ⟨hE',h2⟩ := Finset.mem_powersetCard.mp hE
    obtain ⟨u,v,huv,rfl⟩ := Finset.card_eq_two.mp h2
    have huS : u ∈ S := (Finset.mem_sdiff.mp (hE' (show u ∈ ({u,v} : Finset α) by simp))).1
    have hvS : v ∈ S := (Finset.mem_sdiff.mp (hE' (show v ∈ ({u,v} : Finset α) by simp))).1
    obtain ⟨T,⟨hTB,huT,hvT⟩,_⟩ := hD.2 u huS v hvS huv
    have hN : (A ∩ T).Nonempty := by
      by_contra h0
      apply hn
      refine ⟨T,hTB,Finset.disjoint_left.mpr ?_⟩
      intro x hx hy
      exact h0 ⟨x,Finset.mem_inter.mpr ⟨hx,hy⟩⟩
    exact mem_blockLinks.mpr ⟨hE',h2,T,hTB,
      Finset.insert_subset_iff.mpr ⟨huT,Finset.singleton_subset_iff.mpr hvT⟩,hN⟩
  have h := Finset.card_le_card hsub
  rw [Finset.card_powersetCard,h8] at h
  change 28 ≤ (blockLinks S B A).card at h
  omega

/-- In a four-block with eight outsiders, if at most six outside pairs
link through the block then the remaining groups and an outside block
supply at least eleven independent witnesses away from any selected pair. -/
theorem away_card_ge_eleven_of_four_block_eight_six {S : Finset α} {B : Finset (Finset α)}
    {A : Finset α} {p q b c : α} (hD : PairDesign S B) (hA : A ∈ B)
    (hp : p ∈ A) (hq : q ∈ A) (hb : b ∈ A) (hc : c ∈ A)
    (hbp : b ≠ p) (hbq : b ≠ q) (hcp : c ≠ p) (hcq : c ≠ q) (hbc : b ≠ c)
    (h8 : (S \ A).card = 8) (h6 : (blockLinks S B A).card ≤ 6) :
    11 ≤ (away B p q).card := by
  classical
  let P := groupsThrough B A b
  let Q := groupsThrough B A c
  obtain ⟨D,hDB,hDA⟩ := exists_block_disjoint_of_eight_six hD h8 h6
  have g₁ := card_groups_add_links_ge_eight hD hA hb h8
  have g₂ := card_groups_add_links_ge_eight hD hA hc h8
  change 8 ≤ P.card + (groupLinks B A b).card at g₁
  change 8 ≤ Q.card + (groupLinks B A c).card at g₂
  have ge := Finset.card_le_card (Finset.union_subset (groupLinks_subset_blockLinks hD hb)
    (groupLinks_subset_blockLinks hD hc))
  rw [Finset.card_union_of_disjoint (disjoint_groupLinks hD hA hb hc hbc)] at ge
  have haway {z : α} (hz : z ∈ A) (hzp : z ≠ p) (hzq : z ≠ q) :
      groupsThrough B A z ⊆ away B p q := by
    intro C hC
    obtain ⟨hCe,hzC⟩ := Finset.mem_filter.mp hC
    obtain ⟨hCne,hCB⟩ := Finset.mem_erase.mp hCe
    exact mem_away.mpr ⟨hCB,
      fun h => hCne (blocks_eq_of_common_pair hD hCB hA hzC h hz hp hzp),
      fun h => hCne (blocks_eq_of_common_pair hD hCB hA hzC h hz hq hzq)⟩
  have hd : Disjoint P Q := by
    apply Finset.disjoint_left.mpr
    intro C hCP hCQ
    obtain ⟨hCe,hbC⟩ := Finset.mem_filter.mp hCP
    obtain ⟨hCne,hCB⟩ := Finset.mem_erase.mp hCe
    exact hCne (blocks_eq_of_common_pair hD hCB hA hbC (Finset.mem_filter.mp hCQ).2 hb hc hbc)
  have hdout : D ∉ P ∪ Q := by
    intro h
    exact (Finset.mem_union.mp h).elim
      (fun he => Finset.disjoint_left.mp hDA hb (Finset.mem_filter.mp he).2)
      (fun he => Finset.disjoint_left.mp hDA hc (Finset.mem_filter.mp he).2)
  have hDaway : D ∈ away B p q := mem_away.mpr ⟨hDB,
    Finset.disjoint_left.mp hDA hp,Finset.disjoint_left.mp hDA hq⟩
  have he := Finset.card_le_card (Finset.insert_subset_iff.mpr ⟨hDaway,
    Finset.union_subset (haway hb hbp hbq) (haway hc hcp hcq)⟩)
  rw [Finset.card_insert_of_notMem hdout,Finset.card_union_of_disjoint hd] at he
  omega

#print axioms away_card_ge_eleven_of_four_block_eight_six
end FranklBlockIncidence

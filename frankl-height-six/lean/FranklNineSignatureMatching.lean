import FranklFourBlockGroups

open scoped BigOperators
namespace FranklBlockIncidence
variable {α : Type*} [DecidableEq α]

/-- For a triple block in a pair design with blocks of size at most three,
the links are a union of three matchings, one for each point in the block. -/
theorem card_links_in_subset_le_three_half {S : Finset α} {B : Finset (Finset α)}
    {A : Finset α} (hD : PairDesign S B) (h3 : ∀ T ∈ B, T.card ≤ 3) (hA3 : A.card = 3)
    (V : Finset α) :
    ((blockLinks S B A).filter (· ⊆ V)).card ≤ 3 * (V.card / 2) := by
  classical
  let F (b : α) := (groupLinks B A b).filter (· ⊆ V)
  have hCover : (blockLinks S B A).filter (· ⊆ V) ⊆ A.biUnion F := by
    intro e he
    obtain ⟨heL,heV⟩ := Finset.mem_filter.mp he
    obtain ⟨heS,he2,T,hTB,heT,hN⟩ := mem_blockLinks.mp heL
    obtain ⟨b,hb⟩ := hN
    obtain ⟨hbA,hbT⟩ := Finset.mem_inter.mp hb
    obtain ⟨u,hu⟩ := Finset.card_pos.mp (show 0 < e.card by omega)
    have hn : T ≠ A := fun heq => (Finset.mem_sdiff.mp (heS hu)).2 (heq ▸ heT hu)
    have hbG : T ∈ groupsThrough B A b :=
      Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hn,hTB⟩,hbT⟩
    have heG : e ∈ groupLinks B A b :=
      Finset.mem_biUnion.mpr ⟨T,hbG,Finset.mem_powersetCard.mpr
        ⟨fun x hx => Finset.mem_sdiff.mpr ⟨heT hx,(Finset.mem_sdiff.mp (heS hx)).2⟩,he2⟩⟩
    exact Finset.mem_biUnion.mpr ⟨b,hbA,Finset.mem_filter.mpr ⟨heG,heV⟩⟩
  have hF (b : α) (hbA : b ∈ A) : (F b).card ≤ V.card / 2 := by
    have hsize (e : Finset α) (he : e ∈ F b) : e.card = 2 := by
      obtain ⟨T,_,h⟩ := Finset.mem_biUnion.mp (Finset.mem_filter.mp he).1
      exact (Finset.mem_powersetCard.mp h).2
    have hDisj : (F b : Set (Finset α)).PairwiseDisjoint id := by
      intro e he g hg hne
      apply Finset.disjoint_left.mpr
      intro x hxE hxG
      obtain ⟨T,hT,hE⟩ := Finset.mem_biUnion.mp (Finset.mem_filter.mp he).1
      obtain ⟨R,hR,hG⟩ := Finset.mem_biUnion.mp (Finset.mem_filter.mp hg).1
      obtain ⟨hET,he2⟩ := Finset.mem_powersetCard.mp hE
      obtain ⟨hGR,hg2⟩ := Finset.mem_powersetCard.mp hG
      have hTB := (Finset.mem_erase.mp (Finset.mem_filter.mp hT).1).2
      have hRB := (Finset.mem_erase.mp (Finset.mem_filter.mp hR).1).2
      have hbT := (Finset.mem_filter.mp hT).2
      have hbR := (Finset.mem_filter.mp hR).2
      obtain ⟨hxT,hxA⟩ := Finset.mem_sdiff.mp (hET hxE)
      have heq := blocks_eq_of_common_pair hD hTB hRB hbT hxT hbR (Finset.mem_sdiff.mp (hGR hxG)).1
        (fun eq => hxA (eq ▸ hbA))
      have hcap : (T \ A).card ≤ 2 := by
        have hh := Finset.card_sdiff_add_card_inter T A
        have hpos : 0 < (T ∩ A).card := Finset.card_pos.mpr ⟨b,Finset.mem_inter.mpr ⟨hbT,hbA⟩⟩
        have hcard := h3 T hTB
        omega
      have hEeq := Finset.eq_of_subset_of_card_le hET (show (T \ A).card ≤ e.card by omega)
      have hGR' : g ⊆ T \ A := heq.symm ▸ hGR
      have hGeq := Finset.eq_of_subset_of_card_le hGR' (show (T \ A).card ≤ g.card by omega)
      exact hne (hEeq.trans hGeq.symm)
    have hsub : (F b).biUnion id ⊆ V := by
      intro x hx
      obtain ⟨e,he,hxe⟩ := Finset.mem_biUnion.mp hx
      exact (Finset.mem_filter.mp he).2 hxe
    have hC := Finset.card_le_card hsub
    rw [Finset.card_biUnion hDisj] at hC
    have hh : (∑ e ∈ F b, (id e).card) = ∑ _e ∈ F b, 2 :=
      Finset.sum_congr rfl (fun e he => hsize e he)
    rw [hh,Finset.sum_const,nsmul_eq_mul] at hC
    change (F b).card * 2 ≤ V.card at hC
    omega
  have h₁ := Finset.card_le_card hCover
  have h₂ := Finset.card_biUnion_le (s := A) (t := F)
  have h₃ := Finset.sum_le_sum (s := A) (fun b hb => hF b hb)
  have hh := h₁.trans (h₂.trans h₃)
  simpa [hA3] using hh

/-- Eight equal-label pairs on nine points leave at most four labels, if
each subset inherits the edge bound of a union of three matchings. -/
theorem image_card_le_four_of_nine_matchings {β : Type*} [DecidableEq β]
    {E : Finset α} {P : Finset (Finset α)} (f : α → β)
    (hE : E.card = 9) (hP : 8 ≤ P.card)
    (hedge : ∀ e ∈ P, e ⊆ E ∧ e.card = 2 ∧ ∀ u ∈ e, ∀ v ∈ e, f u = f v)
    (hMatch : ∀ V : Finset α, (P.filter (· ⊆ V)).card ≤ 3*(V.card/2)) :
    (E.image f).card ≤ 4 := by
  classical
  by_contra! hn
  let L := E.image f
  let V (b : β) := E.filter (fun u => f u = b)
  let n (b : β) := (V b).card
  let M (b : β) := P.filter (· ⊆ V b)
  have hnL : 5 ≤ L.card := by exact hn
  have hpos (b : β) (hb : b ∈ L) : 1 ≤ n b := by
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hb
    exact Finset.card_pos.mpr ⟨u,Finset.mem_filter.mpr ⟨hu,rfl⟩⟩
  have hsum : ∑ b ∈ L, n b = 9 := by
    rw [← hE]
    exact (Finset.card_eq_sum_card_image f E).symm
  have hEx : (∑ b ∈ L, (n b - 1)) + L.card = 9 := by
    have he : (∑ b ∈ L, ((n b - 1)+1)) = ∑ b ∈ L, n b := by
      apply Finset.sum_congr rfl
      intro b hb
      have hp := hpos b hb
      omega
    rw [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,mul_one,hsum] at he
    exact he
  have hEx4 : (∑ b ∈ L, (n b - 1)) ≤ 4 := by omega
  have hmax (b : β) (hb : b ∈ L) : n b ≤ 5 := by
    have he := Finset.single_le_sum (f := fun d => n d - 1) (fun _ _ => Nat.zero_le _) hb
    omega
  have hCover : P ⊆ L.biUnion M := by
    intro e he
    obtain ⟨hs,h2,hlabels⟩ := hedge e he
    obtain ⟨u,hu⟩ := Finset.card_pos.mp (show 0 < e.card by omega)
    exact Finset.mem_biUnion.mpr ⟨f u,Finset.mem_image_of_mem f (hs hu),Finset.mem_filter.mpr
      ⟨he,fun v hv => Finset.mem_filter.mpr ⟨hs hv,hlabels v hv u hu⟩⟩⟩
  have hcount : P.card ≤ ∑ b ∈ L, (M b).card :=
    (Finset.card_le_card hCover).trans Finset.card_biUnion_le
  have hpoint (b : β) (hb : b ∈ L) :
      2*(M b).card ≤ 3*(n b-1) + (if n b = 4 then 3 else 0) := by
    have hMpow : M b ⊆ (V b).powersetCard 2 := by
      intro e he
      obtain ⟨heP,hes⟩ := Finset.mem_filter.mp he
      exact Finset.mem_powersetCard.mpr ⟨hes,(hedge e heP).2.1⟩
    have h₁ := Finset.card_le_card hMpow
    rw [Finset.card_powersetCard] at h₁
    change (M b).card ≤ (n b).choose 2 at h₁
    have h₂ := hMatch (V b)
    change (M b).card ≤ 3*(n b / 2) at h₂
    have h₃ := hmax b hb
    have h₄ := hpos b hb
    generalize he : n b = c at h₁ h₂ h₃ h₄ ⊢
    interval_cases c <;> norm_num at * <;> omega
  have hpt := Finset.sum_le_sum (s := L) hpoint
  rw [← Finset.mul_sum,Finset.sum_add_distrib,← Finset.mul_sum] at hpt
  have hRare : (∑ b ∈ L, if n b = 4 then 3 else 0) ≤ 3 := by
    have hRR : (∑ b ∈ L, (3*(if n b=4 then 1 else 0))) ≤ ∑ b ∈ L, (n b-1) := by
      apply Finset.sum_le_sum
      intro b hb
      split <;> omega
    rw [← Finset.mul_sum,← Finset.card_filter] at hRR
    have hh : (∑ b ∈ L, if n b=4 then 3 else 0) =
        3*(L.filter (fun b => n b=4)).card := by
      have hh' : (∑ b ∈ L, if n b=4 then 3 else 0) =
          ∑ b ∈ L, (3*(if n b=4 then 1 else 0)) := by
        apply Finset.sum_congr rfl
        intro b _
        split <;> simp
      rw [hh',← Finset.mul_sum,← Finset.card_filter]
    rw [hh]
    omega
  omega

#print axioms card_links_in_subset_le_three_half
#print axioms image_card_le_four_of_nine_matchings
end FranklBlockIncidence

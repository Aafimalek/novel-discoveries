import FranklNineSignatureMatching

open scoped BigOperators
namespace FranklBlockIncidence
variable {α : Type*} [DecidableEq α]

theorem equal_label_pairs_card_le_ten {β : Type*} [DecidableEq β] {E : Finset α}
    (f : α → β) (hE : E.card = 9) (hL : 5 ≤ (E.image f).card) :
    (((E.image f).biUnion (fun y => (E.filter (fun x => f x = y)).powersetCard 2))).card ≤ 10 := by
  let L := E.image f
  let c (y : β) := (E.filter (fun x => f x = y)).card
  have hcPos (y : β) (hy : y ∈ L) : 1 ≤ c y := by
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    exact Finset.card_pos.mpr ⟨x,Finset.mem_filter.mpr ⟨hx,rfl⟩⟩
  have hsum : E.card = ∑ y ∈ L, c y := Finset.card_eq_sum_card_image f E
  have hparts : (∑ y ∈ L, (c y-1)) + L.card = E.card := by
    have hc : (∑ y ∈ L, ((c y-1) + 1)) = ∑ y ∈ L,c y := by
      apply Finset.sum_congr rfl
      intro y hy
      have hpos := hcPos y hy
      omega
    rw [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,mul_one,← hsum] at hc
    exact hc
  have hbound (y : β) (hy : y ∈ L) : c y ≤ 5 := by
    have h₁ : c y-1 ≤ ∑ z ∈ L, (c z-1) := Finset.single_le_sum (f := fun z => c z-1) (fun _ _ => Nat.zero_le _) hy
    change 5 ≤ L.card at hL
    omega
  have hnum (n : ℕ) (hn : n ≤ 5) : 2*n.choose 2 ≤ 5*(n-1) := by interval_cases n <;> decide
  have hz := Finset.card_biUnion_le (s := L) (t := fun y => (E.filter (fun x => f x = y)).powersetCard 2)
  simp only [Finset.card_powersetCard] at hz
  change ((L.biUnion (fun y => (E.filter (fun x => f x = y)).powersetCard 2))).card ≤ ∑ y ∈ L, (c y).choose 2 at hz
  have hsumle : (∑ y ∈ L, 2*(c y).choose 2) ≤ ∑ y ∈ L, 5*(c y-1) :=
    Finset.sum_le_sum (fun y hy => hnum (c y) (hbound y hy))
  rw [← Finset.mul_sum,← Finset.mul_sum] at hsumle
  change 5 ≤ L.card at hL
  change ((L.biUnion (fun y => (E.filter (fun x => f x = y)).powersetCard 2))).card ≤ 10
  omega

theorem image_card_le_four_of_ten_matchings {β : Type*} [DecidableEq β]
    {E : Finset α} {P : Finset (Finset α)} (f : α → β)
    (hE : E.card = 10) (hP : 10 ≤ P.card)
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
  have hsum : ∑ b ∈ L, n b = 10 := by
    rw [← hE]
    exact (Finset.card_eq_sum_card_image f E).symm
  have hEx : (∑ b ∈ L, (n b - 1)) + L.card = 10 := by
    have he : (∑ b ∈ L, ((n b - 1)+1)) = ∑ b ∈ L, n b := by
      apply Finset.sum_congr rfl
      intro b hb
      have hp := hpos b hb
      omega
    rw [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,mul_one,hsum] at he
    exact he
  have hEx5 : (∑ b ∈ L, (n b - 1)) ≤ 5 := by omega
  have hmax (b : β) (hb : b ∈ L) : n b ≤ 6 := by
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
      2*(M b).card ≤ 3*(n b-1) + (if n b = 4 ∨ n b = 6 then 3 else 0) := by
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
  have hRare : (∑ b ∈ L, if n b = 4 ∨ n b = 6 then 3 else 0) ≤ 3 := by
    have hRR : (∑ b ∈ L, (3*(if n b=4 ∨ n b=6 then 1 else 0))) ≤ ∑ b ∈ L, (n b-1) := by
      apply Finset.sum_le_sum
      intro b hb
      split <;> omega
    rw [← Finset.mul_sum,← Finset.card_filter] at hRR
    have hh : (∑ b ∈ L, if n b=4 ∨ n b=6 then 3 else 0) =
        3*(L.filter (fun b => n b=4 ∨ n b=6)).card := by
      have hh' : (∑ b ∈ L, if n b=4 ∨ n b=6 then 3 else 0) =
          ∑ b ∈ L, (3*(if n b=4 ∨ n b=6 then 1 else 0)) := by
        apply Finset.sum_congr rfl
        intro b _
        split <;> simp
      rw [hh',← Finset.mul_sum,← Finset.card_filter]
    rw [hh]
    omega
  omega

#print axioms equal_label_pairs_card_le_ten
#print axioms image_card_le_four_of_ten_matchings
end FranklBlockIncidence

namespace FranklForcingFiber
open FranklBlockIncidence
variable {α : Type*} [DecidableEq α]

theorem pair_fiber_le_thirtytwo_of_nine_eleven {G : Finset (Finset α)}
    {A : Finset α} {p q : α}
    (hG : NoStrictMajority G) (hmin : WeakMinimalGround G)
    (hI : (isolated G).card = 1)
    (hp : p ∈ sources G) (hq : q ∈ sources G) (hpq : p ≠ q) (hpA : p ∈ A) (hqA : q ∈ A)
    (hEq : A = omittedStars G (starPairMax G p q))
    (h9 : (sources G \ A).card = 9) (h11 : 11 ≤ (blockLinks (sources G) (starBlocks G) A).card) :
    (avoidBoth G (starLeaf G p) (starLeaf G q)).card ≤ 32 := by
  let E := sources G \ A
  let K := compressPair G p q (starLeaf G p) (starLeaf G q)
  let f := signature K
  have hlabels : (E.image f).card ≤ 4 := by
    by_contra! hbad
    have h10 := equal_label_pairs_card_le_ten f h9 (show 5 ≤ (E.image f).card by omega)
    have hsub : blockLinks (sources G) (starBlocks G) A ⊆ (E.image f).biUnion
        (fun y => (E.filter (fun z => f z = y)).powersetCard 2) := by
      intro D hD
      obtain ⟨hEs,hD2,_⟩ := mem_blockLinks.mp hD
      obtain ⟨u,hu⟩ := Finset.card_pos.mp (show 0 < D.card by omega)
      exact Finset.mem_biUnion.mpr ⟨f u,Finset.mem_image_of_mem f (hEs hu),
        Finset.mem_powersetCard.mpr ⟨fun v hv => Finset.mem_filter.mpr ⟨hEs hv,
          compressed_pair_signatures_eq_of_blockLink hG hmin hp hq hpq hpA hqA hEq hD hv hu⟩,hD2⟩⟩
    have he := Finset.card_le_card hsub
    exact (Nat.not_lt_of_ge (he.trans h10)) h11
  have h := pair_fiber_card_le_pow_block_signatures hG hmin hp hq hpq hEq
  have hd : (E.image f).card + (isolated G).card ≤ 5 := by omega
  exact h.trans (Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hd)

#print axioms pair_fiber_le_thirtytwo_of_nine_eleven
end FranklForcingFiber

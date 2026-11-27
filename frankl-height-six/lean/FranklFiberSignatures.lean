import FranklBlockIncidence
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.IntervalCases

open scoped BigOperators
namespace FranklBlockIncidence
variable {α : Type*} [DecidableEq α]

def signature (N : Finset (Finset α)) (v : α) : Finset (Finset α) :=
  N.filter (v ∈ ·)

/-- Encode a family member by the labels of its points in E and its
individual points in I. Each label must identify identical membership
patterns on the family. -/
theorem family_card_le_pow_signatures {N : Finset (Finset α)} {E I : Finset α}
    (hNI : ∀ A ∈ N, A ⊆ E ∪ I) :
    N.card ≤ 2 ^ ((E.image (signature N)).card + I.card) := by
  let L := E.image (signature N)
  let f (A : Finset α) := ((A ∩ E).image (signature N), A ∩ I)
  have hm : Set.MapsTo f (N : Set (Finset α))
      (L.powerset.product I.powerset : Set (Finset (Finset (Finset α)) × Finset α)) := by
    intro A _
    exact Finset.mem_product.mpr ⟨Finset.mem_powerset.mpr
      (Finset.image_subset_image Finset.inter_subset_right),Finset.mem_powerset.mpr Finset.inter_subset_right⟩
  have hi : Set.InjOn f (N : Set (Finset α)) := by
    intro A hA B hB he
    have h1 := congrArg Prod.fst he
    have h2 := congrArg Prod.snd he
    change (A ∩ E).image (signature N) = (B ∩ E).image (signature N) at h1
    change A ∩ I = B ∩ I at h2
    have hsub {C D : Finset α} (hC : C ∈ N) (hD : D ∈ N)
        (hCD : (C ∩ E).image (signature N) = (D ∩ E).image (signature N))
        (hI : C ∩ I = D ∩ I) : C ⊆ D := by
      intro x hx
      rcases Finset.mem_union.mp (hNI C hC hx) with hE | hI'
      · have hL : signature N x ∈ (D ∩ E).image (signature N) :=
          hCD ▸ Finset.mem_image_of_mem (signature N) (Finset.mem_inter.mpr ⟨hx,hE⟩)
        obtain ⟨y,hy,heq⟩ := Finset.mem_image.mp hL
        have hY : D ∈ signature N y := Finset.mem_filter.mpr ⟨hD,(Finset.mem_inter.mp hy).1⟩
        have hX := heq ▸ hY
        exact (Finset.mem_filter.mp hX).2
      · have hX : x ∈ D ∩ I := hI ▸ Finset.mem_inter.mpr ⟨hx,hI'⟩
        exact (Finset.mem_inter.mp hX).1
    exact Finset.Subset.antisymm (hsub hA hB h1 h2) (hsub hB hA h1.symm h2.symm)
  have hc := Finset.card_le_card_of_injOn f hm hi
  simpa [Finset.card_product,Finset.card_powerset,pow_add,L] using hc

/-- If eight points have at least five distinct labels, at most six
unordered pairs can have the same label. -/
theorem equal_label_pairs_card_le_six {β : Type*} [DecidableEq β] {E : Finset α}
    (f : α → β) (hE : E.card = 8) (hL : 5 ≤ (E.image f).card) :
    (((E.image f).biUnion (fun y => (E.filter (fun x => f x = y)).powersetCard 2))).card ≤ 6 := by
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
  have hbound (y : β) (hy : y ∈ L) : c y ≤ 4 := by
    have h₁ : c y-1 ≤ ∑ z ∈ L, (c z-1) := Finset.single_le_sum (f := fun z => c z-1) (fun _ _ => Nat.zero_le _) hy
    change 5 ≤ L.card at hL
    omega
  have hnum (n : ℕ) (hn : n ≤ 4) : n.choose 2 ≤ 2*(n-1) := by interval_cases n <;> decide
  have hz := Finset.card_biUnion_le (s := L) (t := fun y => (E.filter (fun x => f x = y)).powersetCard 2)
  simp only [Finset.card_powersetCard] at hz
  have hsumle : (∑ y ∈ L, (c y).choose 2) ≤ ∑ y ∈ L, 2*(c y-1) :=
    Finset.sum_le_sum (fun y hy => hnum (c y) (hbound y hy))
  rw [← Finset.mul_sum] at hsumle
  change 5 ≤ L.card at hL
  have hh := hz.trans hsumle
  change ((L.biUnion (fun y => (E.filter (fun x => f x = y)).powersetCard 2))).card ≤ 6
  omega

#print axioms family_card_le_pow_signatures
#print axioms equal_label_pairs_card_le_six

end FranklBlockIncidence

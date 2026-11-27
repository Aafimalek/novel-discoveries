import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Lean.Elab.Tactic.Omega

namespace NineSeparatedSubsetSums

/-- A family on a two-point product with at most one doubled fiber loses
at most one element when projected. -/
theorem project_card_of_unique_double {α : Type*} [DecidableEq α]
    (F : Finset (α × Bool)) (x : α)
    (h : ∀ a, (a, false) ∈ F → (a, true) ∈ F → a = x) :
    F.card ≤ (F.image Prod.fst).card + 1 := by
  let G := F.erase (x, false)
  have inj : ∀ a ∈ G, ∀ b ∈ G, Prod.fst a = Prod.fst b → a = b := by
    rintro ⟨a, i⟩ ha ⟨b, j⟩ hb he
    change a = b at he
    subst b
    have haF : (a, i) ∈ F := Finset.mem_of_mem_erase ha
    have hbF : (a, j) ∈ F := Finset.mem_of_mem_erase hb
    cases i <;> cases j
    · rfl
    · have e := h a haF hbF
      subst a
      exact ((Finset.mem_erase.mp ha).1 rfl).elim
    · have e := h a hbF haF
      subst a
      exact ((Finset.mem_erase.mp hb).1 rfl).elim
    · rfl
  have hG : (G.image Prod.fst).card = G.card := Finset.card_image_of_injOn inj
  have hle := Finset.card_le_card (Finset.image_subset_image (Finset.erase_subset (x, false) F) (f := Prod.fst))
  by_cases hx : (x, false) ∈ F
  · have hc := Finset.card_erase_add_one hx
    change G.card + 1 = F.card at hc
    change (G.image Prod.fst).card ≤ (F.image Prod.fst).card at hle
    omega
  · have hc : G = F := Finset.erase_eq_of_notMem hx
    rw [hc] at hG
    omega

/-- Any subset containing more than half the vertices of a two-point
product contains one of its matching edges. -/
theorem large_product_has_pair {α : Type*} [DecidableEq α] [Fintype α]
    (P : Finset (α × Bool)) (h : Fintype.card α < P.card) :
    ∃ a, (a, false) ∈ P ∧ (a, true) ∈ P := by
  classical
  by_contra hn
  have inj : ∀ a ∈ P, ∀ b ∈ P, Prod.fst a = Prod.fst b → a = b := by
    rintro ⟨a, i⟩ ha ⟨b, j⟩ hb he
    change a = b at he
    subst b
    cases i <;> cases j
    · rfl
    · exact (hn ⟨a, ha, hb⟩).elim
    · exact (hn ⟨a, hb, ha⟩).elim
    · rfl
  have hc : (P.image Prod.fst).card = P.card := Finset.card_image_of_injOn inj
  have hl := Finset.card_le_univ (P.image Prod.fst)
  omega

#print axioms project_card_of_unique_double
#print axioms large_product_has_pair

end NineSeparatedSubsetSums

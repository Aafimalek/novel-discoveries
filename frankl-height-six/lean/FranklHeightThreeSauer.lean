import Mathlib.Combinatorics.SetFamily.Shatter
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset

namespace FranklHeightThreeSauer

variable {α : Type*} [DecidableEq α]

/-- There are no four distinct members in an inclusion chain. -/
def NoFourChain (G : Finset (Finset α)) : Prop :=
  ∀ ⦃A B C D⦄, A ∈ G → B ∈ G → C ∈ G → D ∈ G →
    A ⊂ B → B ⊂ C → C ⊂ D → False

private lemma witness_mem_iff {S A : Finset α} {x y : α} (h : S ∩ A = {x}) (hy : y ∈ S) :
    y ∈ A ↔ y = x := by
  constructor
  · intro ha
    have : y ∈ S ∩ A := Finset.mem_inter.mpr ⟨hy,ha⟩
    simpa [h] using this
  · rintro rfl
    have : y ∈ S ∩ A := by rw [h]; simp
    exact (Finset.mem_inter.mp this).2

private lemma strict_union {A B : Finset α} {x : α} (ha : x ∉ A) (hb : x ∈ B) :
    A ⊂ A ∪ B := by
  refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_union_left, ?_⟩
  intro eq
  exact ha (eq.symm ▸ Finset.mem_union_right A hb)

/-- In a union-closed family, a shattered triple builds a chain of length four. -/
theorem shatter_card_le_two {G : Finset (Finset α)} {S : Finset α}
    (hU : ∀ ⦃A B⦄, A ∈ G → B ∈ G → A ∪ B ∈ G)
    (hH : NoFourChain G) (hs : G.Shatters S) : S.card ≤ 2 := by
  by_contra! hlarge
  obtain ⟨x,y,z,hx,hy,hz,hxy,hxz,hyz⟩ := Finset.two_lt_card_iff.mp hlarge
  obtain ⟨N,hN,hn⟩ := hs (Finset.empty_subset S)
  obtain ⟨A,hA,ha⟩ := hs.exists_inter_eq_singleton hx
  obtain ⟨B,hB,hb⟩ := hs.exists_inter_eq_singleton hy
  obtain ⟨C,hC,hc⟩ := hs.exists_inter_eq_singleton hz
  have hn' (u) (hu : u ∈ S) : u ∉ N := by
    intro hmem
    have hh : u ∈ S ∩ N := Finset.mem_inter.mpr ⟨hu,hmem⟩
    simp [hn] at hh
  have h1 : N ⊂ N ∪ A := strict_union (hn' x hx) ((witness_mem_iff ha hx).2 rfl)
  have h2 : N ∪ A ⊂ (N ∪ A) ∪ B := by
    apply strict_union (x := y) ?_ ((witness_mem_iff hb hy).2 rfl)
    rw [Finset.mem_union, not_or]
    exact ⟨hn' y hy, fun h => hxy ((witness_mem_iff ha hy).1 h).symm⟩
  have h3 : (N ∪ A) ∪ B ⊂ ((N ∪ A) ∪ B) ∪ C := by
    apply strict_union (x := z) ?_ ((witness_mem_iff hc hz).2 rfl)
    simp only [Finset.mem_union, not_or]
    exact ⟨⟨hn' z hz, fun h => hxz ((witness_mem_iff ha hz).1 h).symm⟩,
      fun h => hyz ((witness_mem_iff hb hz).1 h).symm⟩
  exact hH hN (hU hN hA) (hU (hU hN hA) hB) (hU (hU (hU hN hA) hB) hC) h1 h2 h3

/-- A union-closed family of height at most three on a support of size
d contains at most 1+d+choose(d,2) distinct sets. -/
theorem card_le {G : Finset (Finset α)} (T : Finset α)
    (hU : ∀ ⦃A B⦄, A ∈ G → B ∈ G → A ∪ B ∈ G)
    (hH : NoFourChain G) (hT : ∀ ⦃A⦄, A ∈ G → A ⊆ T) :
    G.card ≤ 1 + T.card + T.card.choose 2 := by
  have hsub : G.shatterer ⊆ (T.powersetCard 0 ∪ T.powersetCard 1) ∪ T.powersetCard 2 := by
    intro S hS
    have hsh := Finset.mem_shatterer.mp hS
    have hsz := shatter_card_le_two hU hH hsh
    obtain ⟨A,hA,hSA⟩ := hsh.exists_superset
    have hST := hSA.trans (hT hA)
    have hs : S.card = 0 ∨ S.card = 1 ∨ S.card = 2 := by omega
    simp only [Finset.mem_union, Finset.mem_powersetCard]
    rcases hs with hs|hs|hs
    · exact Or.inl (Or.inl ⟨hST,hs⟩)
    · exact Or.inl (Or.inr ⟨hST,hs⟩)
    · exact Or.inr ⟨hST,hs⟩
  calc
    G.card ≤ G.shatterer.card := Finset.card_le_card_shatterer G
    _ ≤ ((T.powersetCard 0 ∪ T.powersetCard 1) ∪ T.powersetCard 2).card :=
      Finset.card_le_card hsub
    _ ≤ (T.powersetCard 0 ∪ T.powersetCard 1).card + (T.powersetCard 2).card :=
      Finset.card_union_le _ _
    _ ≤ ((T.powersetCard 0).card + (T.powersetCard 1).card) + (T.powersetCard 2).card :=
      Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ = 1 + T.card + T.card.choose 2 := by simp [Finset.card_powersetCard]

#print axioms shatter_card_le_two
#print axioms card_le

end FranklHeightThreeSauer

import LatinGap

namespace LatinGap
open Finset
private theorem triangle_edge {α : Type} [DecidableEq α]
    {x y z : α} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {S : Finset α} (hc : S.card = 2)
    (hA : ∃ u ∈ S, u ∈ ({x,y} : Finset α))
    (hB : ∃ u ∈ S, u ∈ ({x,z} : Finset α))
    (hC : ∃ u ∈ S, u ∈ ({y,z} : Finset α)) :
    S = {x,y} ∨ S = {x,z} ∨ S = {y,z} := by
  obtain ⟨a,b,hab,rfl⟩ := card_eq_two.mp hc
  simp only [mem_insert,mem_singleton] at hA hB hC
  have swap (a b : α) : ({a,b} : Finset α) = {b,a} := by
    ext c
    simp [or_comm]
  grind

/-- Four distinct two-element sets which pairwise meet have a common member. -/
theorem four_pairs_intersection {α : Type} [DecidableEq α] (A : Fin 4 → Finset α)
    (hcard : ∀ i, (A i).card = 2) (hinj : Function.Injective A)
    (hmeet : ∀ i j, i ≠ j → ∃ u ∈ A i, u ∈ A j) :
    ∃ u, ∀ i, u ∈ A i := by
  classical
  by_contra! H
  obtain ⟨x,y,hxy,h0⟩ := card_eq_two.mp (hcard 0)
  obtain ⟨i,hi⟩ := H x
  obtain ⟨j,hj⟩ := H y
  have hi0 : i ≠ 0 := by
    intro h; subst i
    exact hi (by simp [h0])
  have hj0 : j ≠ 0 := by
    intro h; subst j
    exact hj (by simp [h0])
  have hyi : y ∈ A i := by
    obtain ⟨u,hu,hu0⟩ := hmeet i 0 hi0
    simp only [h0,mem_insert,mem_singleton] at hu0
    rcases hu0 with rfl | rfl
    · exact (hi hu).elim
    · exact hu
  have hxj : x ∈ A j := by
    obtain ⟨u,hu,hu0⟩ := hmeet j 0 hj0
    simp only [h0,mem_insert,mem_singleton] at hu0
    rcases hu0 with rfl | rfl
    · exact hu
    · exact (hj hu).elim
  have hij : i ≠ j := by
    intro h
    exact hi (by simpa only [h] using hxj)
  obtain ⟨z,zi,zj⟩ := hmeet i j hij
  have hxz : x ≠ z := fun e => hi (by simpa only [e] using zi)
  have hyz : y ≠ z := fun e => hj (by simpa only [e] using zj)
  have hi' : A i = {y,z} := by
    refine (eq_of_subset_of_card_le ?_ ?_).symm
    · intro w hw
      simp only [mem_insert,mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact hyi
      · exact zi
    · rw [hcard,card_pair_eq_two_iff.mpr hyz]
  have hj' : A j = {x,z} := by
    refine (eq_of_subset_of_card_le ?_ ?_).symm
    · intro w hw
      simp only [mem_insert,mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact hxj
      · exact zj
    · rw [hcard,card_pair_eq_two_iff.mpr hxz]
  let prev : Finset (Fin 4) := {0,i,j}
  have out : ∃ k : Fin 4, k ∉ prev := by
    by_contra! h
    have card4 : (univ : Finset (Fin 4)).card = 4 := by decide
    have card3 : prev.card ≤ 3 := by
      change (insert 0 (insert i ({j} : Finset (Fin 4)))).card ≤ 3
      have h1 := card_insert_le (a := (0 : Fin 4)) (s := insert i ({j} : Finset (Fin 4)))
      have h2 := card_insert_le (a := i) (s := ({j} : Finset (Fin 4)))
      rw [card_singleton] at h2
      omega
    have hb : (univ : Finset (Fin 4)) ⊆ prev := fun a _ => h a
    have := card_le_card hb
    omega
  obtain ⟨k,hk⟩ := out
  have hk0 : k ≠ 0 := by intro e; simp [prev,e] at hk
  have hki : k ≠ i := by intro e; simp [prev,e] at hk
  have hkj : k ≠ j := by intro e; simp [prev,e] at hk
  have hit := triangle_edge hxy hxz hyz (hcard k)
    (by simpa only [h0] using hmeet k 0 hk0) (by simpa only [hj'] using hmeet k j hkj) (by simpa only [hi'] using hmeet k i hki)
  rcases hit with h|h|h
  · exact hk0 (hinj (h.trans h0.symm))
  · exact hkj (hinj (h.trans hj'.symm))
  · exact hki (hinj (h.trans hi'.symm))

/-- In a linear design, if four chosen degree-two labels make all six pair
projections, one word contains all four labels. -/
theorem all_used_low_word {n : ℕ} {D : Design n} (hD : Linear D)
    (a : Word n) (hl : ∀ i, freq D (i,a i) = 2)
    (hall : ∀ i j, i ≠ j → Used D (i,a i) (j,a j)) :
    a ∈ D := by
  classical
  let A (i : Fin 4) := incident D (i,a i)
  have hc (i : Fin 4) : (A i).card = 2 := hl i
  have hi : Function.Injective A := by
    intro i j hij
    by_contra hn
    obtain ⟨u,v,huv,huvA⟩ := card_eq_two.mp (hc i)
    have hu' : u ∈ A i := by simp [huvA]
    have hv' : v ∈ A i := by simp [huvA]
    have hju' : u ∈ A j := by simpa only [hij] using hu'
    have hjv' : v ∈ A j := by simpa only [hij] using hv'
    obtain ⟨hu, hui⟩ := mem_filter.mp hu'
    obtain ⟨hv, hvi⟩ := mem_filter.mp hv'
    have huj := (mem_filter.mp hju').2
    have hvj := (mem_filter.mp hjv').2
    exact huv (hD hu hv hn (hui.trans hvi.symm) (huj.trans hvj.symm))
  have hm (i j : Fin 4) (h : i ≠ j) : ∃ w ∈ A i, w ∈ A j := by
    obtain ⟨_,w,hw,hi,hj⟩ := hall i j h
    exact ⟨w,mem_filter.mpr ⟨hw,hi⟩, mem_filter.mpr ⟨hw,hj⟩⟩
  obtain ⟨w,hw⟩ := four_pairs_intersection A hc hi hm
  have hwa : w = a := funext fun i => (mem_filter.mp (hw i)).2
  simpa only [hwa] using (mem_filter.mp (hw 0)).1

#print axioms four_pairs_intersection
#print axioms all_used_low_word
end LatinGap

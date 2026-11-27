import EulerRename

namespace LatinGap
open Finset

/-- Normalize the minimum-one anchor word to 0000, without changing the
set size or the minimum degree. -/
theorem normalize_degree_one_anchor {D : Design 6} (hD : Linear D) (hS : Saturated D)
    (x : Label 6) (hmin : ∀ y : Label 6, 1 ≤ freq D y) (hx : freq D x = 1) :
    ∃ E : Design 6, Linear E ∧ Saturated E ∧ E.card = D.card ∧
      (∀ y : Label 6, 1 ≤ freq E y) ∧ freq E (0,0) = 1 ∧ (fun _ => 0) ∈ E := by
  obtain ⟨F,hF,hsF,hcard,hfmin,hf0⟩ := normalize_min_label_six hD hS x 1 hmin hx
  have hn : (incident F (0,0)).Nonempty := Finset.card_pos.mp (by change 0 < freq F (0,0); omega)
  obtain ⟨u,hu⟩ := hn
  have huF := (Finset.mem_filter.mp hu).1
  have hu0 : u 0 = 0 := (Finset.mem_filter.mp hu).2
  let lab : Coord → Fin 6 ≃ Fin 6 := fun i => Equiv.swap (u i) 0
  let I : Coord ≃ Coord := Equiv.refl _
  let E := renameDesign I lab F
  refine ⟨E,renameDesign_linear hF _ _,renameDesign_saturated hsF _ _,
    (renameDesign_card _ _ _).trans hcard,?_,?_,?_⟩
  · rintro ⟨i,a⟩
    have h := renameDesign_freq I lab F i ((lab i).symm a)
    rw [(lab i).apply_symm_apply] at h
    exact h.symm ▸ hfmin (I i,(lab i).symm a)
  · have h := renameDesign_freq I lab F 0 (0 : Fin 6)
    have he : lab 0 0 = 0 := by simp [lab,hu0]
    rw [he] at h
    exact h.trans hf0
  · refine Finset.mem_map.mpr ⟨u,huF,?_⟩
    funext i
    change lab i (u i) = 0
    exact Equiv.swap_apply_left _ _

/-- A degree-two anchor has exactly two distinct incident words. They can
be normalized to 0000 and 0111 (first coordinate zero) simultaneously. -/
theorem normalize_degree_two_anchor {D : Design 6} (hD : Linear D) (hS : Saturated D)
    (x : Label 6) (hmin : ∀ y : Label 6, 2 ≤ freq D y) (hx : freq D x = 2) :
    ∃ E : Design 6, Linear E ∧ Saturated E ∧ E.card = D.card ∧
      (∀ y : Label 6, 2 ≤ freq E y) ∧ freq E (0,0) = 2 ∧
      (fun _ => 0) ∈ E ∧ (fun i => if i = 0 then 0 else 1) ∈ E := by
  obtain ⟨F,hF,hsF,hcard,hfmin,hf0⟩ := normalize_min_label_six hD hS x 2 hmin hx
  obtain ⟨u,v,huv,huvset⟩ := Finset.card_eq_two.mp (show (incident F (0,0)).card = 2 from hf0)
  have hu : u ∈ incident F (0,0) := by rw [huvset]; simp
  have hv : v ∈ incident F (0,0) := by rw [huvset]; simp
  have huF := (Finset.mem_filter.mp hu).1
  have hvF := (Finset.mem_filter.mp hv).1
  have hu0 : u 0 = 0 := (Finset.mem_filter.mp hu).2
  have hv0 : v 0 = 0 := (Finset.mem_filter.mp hv).2
  have diff (i : Coord) (hi : i ≠ 0) : u i ≠ v i :=
    fun h => huv (hF huF hvF hi h (hu0.trans hv0.symm))
  let first : Coord → Fin 6 ≃ Fin 6 := fun i => Equiv.swap (u i) 0
  let lab : Coord → Fin 6 ≃ Fin 6 := fun i =>
    (first i).trans (Equiv.swap (first i (v i)) (if i = 0 then 0 else 1))
  let I : Coord ≃ Coord := Equiv.refl _
  let E := renameDesign I lab F
  have lab_u (i : Coord) : lab i (u i) = 0 := by
    change Equiv.swap (first i (v i)) (if i = 0 then 0 else 1) (first i (u i)) = 0
    rw [show first i (u i) = 0 from Equiv.swap_apply_left _ _]
    by_cases hi : i = 0
    · subst i
      simp [first,hu0,hv0]
    · rw [ite_eq_right hi]
      apply Equiv.swap_apply_of_ne_of_ne
      · intro he
        exact diff i hi ((first i).injective ((show first i (u i) = 0 from Equiv.swap_apply_left _ _).trans he))
      · decide
  have lab_v (i : Coord) : lab i (v i) = (if i = 0 then 0 else 1) := by
    exact Equiv.swap_apply_left _ _
  refine ⟨E,renameDesign_linear hF _ _,renameDesign_saturated hsF _ _,
    (renameDesign_card _ _ _).trans hcard,?_,?_,?_,?_⟩
  · rintro ⟨i,a⟩
    have h := renameDesign_freq I lab F i ((lab i).symm a)
    rw [(lab i).apply_symm_apply] at h
    exact h.symm ▸ hfmin (I i,(lab i).symm a)
  · have h := renameDesign_freq I lab F 0 (u 0)
    rw [lab_u,hu0] at h
    exact h.trans hf0
  · refine Finset.mem_map.mpr ⟨u,huF,?_⟩
    funext i
    exact lab_u i
  · refine Finset.mem_map.mpr ⟨v,hvF,?_⟩
    funext i
    exact lab_v i

#print axioms normalize_degree_one_anchor
#print axioms normalize_degree_two_anchor
end LatinGap

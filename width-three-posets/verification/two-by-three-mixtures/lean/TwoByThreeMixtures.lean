import TwoByThreeReplay

namespace TwoByThreeReplay

abbrev Weights := Fin 10 → Fin 7 → ℕ

def mass (w : Weights) : ℕ :=
  ∑ p : Fin 10, ∑ k : Fin 7, (k.val+1) * w p k

def count (w : Weights) (u v : Fin 7) : ℕ :=
  ∑ p : Fin 10, ∑ k : Fin 7, component p k u v * w p k

def linearForm (C : Fin 7 → Fin 7 → ℕ) (terms : List Term) : ℕ :=
  (terms.map fun t => coeff t * C (start t) (finish t)).sum

private theorem linearForm_to_components (w : Weights) (terms : List Term) :
    linearForm (count w) terms = ∑ p : Fin 10, ∑ k : Fin 7, componentForm terms p k * w p k := by
  induction terms with
  | nil => simp [linearForm, componentForm]
  | cons t ts ih =>
    have hL : linearForm (count w) (t::ts) =
        coeff t * (count w (start t) (finish t)) + linearForm (count w) ts := rfl
    rw [hL, ih]
    unfold count
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro k _
    simp only [componentForm, List.map_cons, List.sum_cons, Nat.add_mul, Nat.mul_assoc]

/-- Lift a finite per-component certificate to any nonnegative integer mixture. -/
theorem linearForm_le_of_component (terms : List Term) (d L : ℕ) (w : Weights)
    (h : ∀ p k, d * componentForm terms p k ≤ L * (k.val+1)) :
    d * linearForm (count w) terms ≤ L * mass w := by
  rw [linearForm_to_components]
  unfold mass
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p _
  apply Finset.sum_le_sum
  intro k _
  simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right (w p k) (h p k)

private theorem count_base_add (w : Weights) : count w 0 6 + count w 6 0 = mass w := by
  have aux : ∀ p k, component p k 0 6 + component p k 6 0 = k.val+1 := by decide
  unfold count mass
  simp only [← Finset.sum_add_distrib, ← Nat.add_mul, aux]

private theorem contradiction_by_row (r : Fin 25) (C : Fin 7 → Fin 7 → ℕ) (N : ℕ)
    (upper : 30 * linearForm C (cert r).1 ≤ (cert r).2 * N)
    (base : 0 < baseCoeff (cert r).1 → 23 * N ≤ 30 * C 0 6)
    (strong : ∀ t ∈ (cert r).1, 2 * N < 3 * C (start t) (finish t)) :
    False := by
  fin_cases r
  ·
    have hXa := strong (2,2,6) (by decide)
    have hZa := strong (3,5,6) (by decide)
    simp [linearForm, cert, coeff, start, finish] at upper
    simp only [start, finish] at hXa hZa
    omega
  ·
    have hXa := strong (1,2,6) (by decide)
    have hYa := strong (1,4,6) (by decide)
    simp [linearForm, cert, coeff, start, finish] at upper
    simp only [start, finish] at hXa hYa
    omega
  ·
    have hax := strong (30,6,1) (by decide)
    have hb := base (by decide)
    have hxY := strong (5,1,4) (by decide)
    have hxZ := strong (3,1,5) (by decide)
    have hxy := strong (10,1,3) (by decide)
    simp [linearForm, cert, coeff, start, finish] at upper
    simp only [start, finish] at hax hxY hxZ hxy
    omega
  ·
    have hay := strong (4,6,3) (by decide)
    have hxa := strong (6,1,6) (by decide)
    have hyX := strong (1,3,2) (by decide)
    simp [linearForm, cert, coeff, start, finish] at upper
    simp only [start, finish] at hay hxa hyX
    omega
  ·
    have hxy := strong (1,1,3) (by decide)
    have hya := strong (7,3,6) (by decide)
    simp [linearForm, cert, coeff, start, finish] at upper
    simp only [start, finish] at hxy hya
    omega
  ·
    have hay := strong (2,6,3) (by decide)
    have hb := base (by decide)
    have hyx := strong (1,3,1) (by decide)
    simp [linearForm, cert, coeff, start, finish] at upper
    simp only [start, finish] at hay hyx
    omega
  ·
    have hax := strong (20,6,1) (by decide)
    have hxY := strong (5,1,4) (by decide)
    have hxZ := strong (3,1,5) (by decide)
    have hya := strong (30,3,6) (by decide)
    simp [linearForm, cert, coeff, start, finish] at upper
    simp only [start, finish] at hax hxY hxZ hya
    omega
  ·
    have hxa := strong (7,1,6) (by decide)
    have hyx := strong (1,3,1) (by decide)
    simp [linearForm, cert, coeff, start, finish] at upper
    simp only [start, finish] at hxa hyx
    omega
  ·
    have hay := strong (6,6,3) (by decide)
    have hb := base (by decide)
    have hyX := strong (1,3,2) (by decide)
    have hyx := strong (2,3,1) (by decide)
    simp [linearForm, cert, coeff, start, finish] at upper
    simp only [start, finish] at hay hyX hyx
    omega
  ·
    have hYa := strong (1,4,6) (by decide)
    simp [linearForm, cert, coeff, start, finish] at upper
    simp only [start, finish] at hYa
    omega
  ·
    have hYa := strong (7,4,6) (by decide)
    have hxy := strong (1,1,3) (by decide)
    simp [linearForm, cert, coeff, start, finish] at upper
    simp only [start, finish] at hYa hxy
    omega
  ·
    have hYa := strong (7,4,6) (by decide)
    have hxY := strong (1,1,4) (by decide)
    simp [linearForm, cert, coeff, start, finish] at upper
    simp only [start, finish] at hYa hxY
    omega
  ·
    have hYx := strong (4,4,1) (by decide)
    have haY := strong (10,6,4) (by decide)
    have hya := strong (15,3,6) (by decide)
    simp [linearForm, cert, coeff, start, finish] at upper
    simp only [start, finish] at hYx haY hya
    omega
  ·
    have hYa := strong (2,4,6) (by decide)
    have hxa := strong (1,1,6) (by decide)
    simp [linearForm, cert, coeff, start, finish] at upper
    simp only [start, finish] at hYa hxa
    omega
  ·
    have haX := strong (2,6,2) (by decide)
    have hay := strong (6,6,3) (by decide)
    have hxa := strong (15,1,6) (by decide)
    simp [linearForm, cert, coeff, start, finish] at upper
    simp only [start, finish] at haX hay hxa
    omega
  ·
    have hXa := strong (1,2,6) (by decide)
    simp [linearForm, cert, coeff, start, finish] at upper
    simp only [start, finish] at hXa
    omega
  ·
    have hXa := strong (2,2,6) (by decide)
    have hya := strong (1,3,6) (by decide)
    simp [linearForm, cert, coeff, start, finish] at upper
    simp only [start, finish] at hXa hya
    omega
  ·
    have hXa := strong (7,2,6) (by decide)
    have hyX := strong (1,3,2) (by decide)
    simp [linearForm, cert, coeff, start, finish] at upper
    simp only [start, finish] at hXa hyX
    omega
  ·
    have hZa := strong (7,5,6) (by decide)
    have hxy := strong (1,1,3) (by decide)
    simp [linearForm, cert, coeff, start, finish] at upper
    simp only [start, finish] at hZa hxy
    omega
  ·
    have hXa := strong (7,2,6) (by decide)
    have hyx := strong (1,3,1) (by decide)
    simp [linearForm, cert, coeff, start, finish] at upper
    simp only [start, finish] at hXa hyx
    omega
  ·
    have hZa := strong (7,5,6) (by decide)
    have hxY := strong (1,1,4) (by decide)
    simp [linearForm, cert, coeff, start, finish] at upper
    simp only [start, finish] at hZa hxY
    omega
  ·
    have hYX := strong (3,4,2) (by decide)
    have hYx := strong (5,4,1) (by decide)
    have haY := strong (20,6,4) (by decide)
    have hya := strong (30,3,6) (by decide)
    simp [linearForm, cert, coeff, start, finish] at upper
    simp only [start, finish] at hYX hYx haY hya
    omega
  ·
    have hZa := strong (7,5,6) (by decide)
    have hxZ := strong (1,1,5) (by decide)
    simp [linearForm, cert, coeff, start, finish] at upper
    simp only [start, finish] at hZa hxZ
    omega
  ·
    have hZa := strong (1,5,6) (by decide)
    simp [linearForm, cert, coeff, start, finish] at upper
    simp only [start, finish] at hZa
    omega
  ·
    have hZa := strong (3,5,6) (by decide)
    have hxa := strong (1,1,6) (by decide)
    simp [linearForm, cert, coeff, start, finish] at upper
    simp only [start, finish] at hZa hxa
    omega

private theorem all_strong_from_fits (w : Weights) (p : Fin 10) (j : Fin 6)
    (terms : List Term) (hfits : fits p j terms = true)
    (strong : ∀ u v : Fin 7, rank p ⟨j.val+1,by omega⟩ u < rank p ⟨j.val+1,by omega⟩ v →
      2 * mass w < 3 * count w u v) :
    ∀ t ∈ terms, 2 * mass w < 3 * count w (start t) (finish t) := by
  intro t ht
  exact strong (start t) (finish t) (of_decide_eq_true (List.all_eq_true.mp hfits t ht))

/-- Numeric conclusion for the 7/30 certificate: no listed majority orientation
of a genuine nonnegative cutoff mixture can have all its comparisons above 2/3. -/
theorem no_strong_majority_7_30 (w : Weights) (p : Fin 10) (j : Fin 6)
    (cap : 30 * count w 6 0 ≤ 7 * mass w)
    (strong : ∀ u v : Fin 7, rank p ⟨j.val+1,by omega⟩ u < rank p ⟨j.val+1,by omega⟩ v →
      2 * mass w < 3 * count w u v) :
    False := by
  obtain ⟨r,hfits,_⟩ := replay_orientation_coverage p j
  have hba := count_base_add w
  have h23 : 23 * mass w ≤ 30 * count w 0 6 := by omega
  exact contradiction_by_row r (count w) (mass w)
    (linearForm_le_of_component _ _ _ w (replay_component_bound r))
    (fun _ => h23) (all_strong_from_fits w p j _ hfits strong)

/-- Quarter variant under the support restriction x<Z. This is still a
theorem about cutoff mixtures, not a classification of rankings of a poset. -/
theorem no_strong_majority_quarter_of_x_before_Z (w : Weights) (p : Fin 10) (j : Fin 6)
    (support : ∀ q k, ¬ branchRank q 1 < branchRank q 5 → w q k = 0)
    (cap : 4 * count w 6 0 ≤ mass w)
    (strong : ∀ u v : Fin 7, rank p ⟨j.val+1,by omega⟩ u < rank p ⟨j.val+1,by omega⟩ v →
      2 * mass w < 3 * count w u v) :
    False := by
  by_cases hj : j = 0
  · subst j
    have hba := count_base_add w
    have hbase : 3 * mass w ≤ 4 * count w 0 6 := by omega
    rcases replay_quarter_early_coverage p with hX | hY
    · have hb : linearForm (count w) quarterX ≤ 15 * mass w := by
        rw [linearForm_to_components]
        unfold mass
        simp only [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro q _
        apply Finset.sum_le_sum
        intro k _
        by_cases h : branchRank q 1 < branchRank q 5
        · simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right (w q k) (replay_quarter_X q k h)
        · simp [support q k h]
      have H := all_strong_from_fits w p 0 _ hX strong
      have h1 := H (6,6,1) (by decide)
      have h2 := H (2,1,3) (by decide)
      have h3 := H (1,1,4) (by decide)
      simp only [linearForm, quarterX, coeff, start, finish, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hb h1 h2 h3
      omega
    · have hb := linearForm_le_of_component quarterY 1 15 w (by simpa using replay_quarter_Y)
      have H := all_strong_from_fits w p 0 _ hY strong
      have h1 := H (6,6,3) (by decide)
      have h2 := H (2,3,1) (by decide)
      have h3 := H (1,3,2) (by decide)
      simp only [linearForm, quarterY, coeff, start, finish, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.one_mul] at hb h1 h2 h3
      omega
  · obtain ⟨r,hfits,hfree⟩ := replay_orientation_coverage p j
    have hr := hfree.resolve_left hj
    exact contradiction_by_row r (count w) (mass w)
      (linearForm_le_of_component _ _ _ w (replay_component_bound r))
      (fun h => (Nat.not_lt_zero _ (hr ▸ h)).elim) (all_strong_from_fits w p j _ hfits strong)

#print axioms no_strong_majority_7_30
#print axioms no_strong_majority_quarter_of_x_before_Z

end TwoByThreeReplay

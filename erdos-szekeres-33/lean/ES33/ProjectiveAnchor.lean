import ES33.FullReduction
import Mathlib.Topology.Order.OrderClosed

namespace ES33

/-- A finite projective chart for moving the chosen point to a positive anchor.
All denominators are positive on the applications considered here. -/
noncomputable def anchorChart (e C : ℝ) (u : Plane) : Plane :=
  ((u.2 + C*u.1)/(u.1+e), -u.1/(u.1+e))

@[simp] theorem anchorChart_zero (e C : ℝ) : anchorChart e C (0,0) = (0,0) := by
  simp [anchorChart]

theorem orient_anchorChart_mul (e C : ℝ) (a b c : Plane)
    (ha : a.1+e ≠ 0) (hb : b.1+e ≠ 0) (hc : c.1+e ≠ 0) :
    orient (anchorChart e C a) (anchorChart e C b) (anchorChart e C c) *
      ((a.1+e)*(b.1+e)*(c.1+e)) = e * orient a b c := by
  simp only [anchorChart,orient]
  field_simp [ha,hb,hc]
  ring

theorem positiveBit_orient_anchorChart (e C : ℝ) (a b c : Plane)
    (he : 0 < e) (ha : 0 < a.1+e) (hb : 0 < b.1+e) (hc : 0 < c.1+e) :
    positiveBit (orient (anchorChart e C a) (anchorChart e C b) (anchorChart e C c)) =
      positiveBit (orient a b c) := by
  have hD : 0 < (a.1+e)*(b.1+e)*(c.1+e) := mul_pos (mul_pos ha hb) hc
  have hei := orient_anchorChart_mul e C a b c ha.ne' hb.ne' hc.ne'
  unfold positiveBit
  congr 1
  rw [← mul_pos_iff_of_pos_right hD, hei, mul_pos_iff_of_pos_left he]

theorem orient_anchorChart_ne (e C : ℝ) (a b c : Plane)
    (he : 0 < e) (ha : 0 < a.1+e) (hb : 0 < b.1+e) (hc : 0 < c.1+e)
    (hor : orient a b c ≠ 0) :
    orient (anchorChart e C a) (anchorChart e C b) (anchorChart e C c) ≠ 0 := by
  intro hh
  have eq := orient_anchorChart_mul e C a b c ha.ne' hb.ne' hc.ne'
  rw [hh, zero_mul] at eq
  exact (mul_ne_zero he.ne' hor) eq.symm

/-- The angular ordering of rays from the origin is their slope ordering. -/
theorem orient_origin_pos_iff_slope (a b : Plane) (ha : 0 < a.1) (hb : 0 < b.1) :
    0 < orient (0,0) a b ↔ a.2 / a.1 < b.2 / b.1 := by
  have h := (div_lt_div_iff₀ ha hb : a.2/a.1 < b.2/b.1 ↔ a.2*b.1 < b.2*a.1)
  rw [h]
  simp only [orient, sub_zero]
  constructor <;> intro hh <;> linarith

/-- An exact pairwise bound for preserving the angular order in a finite chart. -/
theorem anchor_x_lt_of_small {e C : ℝ} {a b : Plane}
    (he : 0 < e) (ha : 0 < a.1) (hb : 0 < b.1)
    (h : a.2 / a.1 < b.2 / b.1)
    (hE : e * (|b.2 + C*b.1 - (a.2 + C*a.1)| + 1) <
      b.2*a.1 - a.2*b.1) :
    (anchorChart e C a).1 < (anchorChart e C b).1 := by
  have hcross := (div_lt_div_iff₀ ha hb).mp h
  apply (div_lt_div_iff₀ (add_pos ha he) (add_pos hb he)).mpr
  have hlow := neg_abs_le (b.2+C*b.1-(a.2+C*a.1))
  have h2 := mul_le_mul_of_nonneg_left hlow he.le
  nlinarith

/-- After translating a leftmost point to the origin and sorting the
remaining points by slope, a single small positive parameter works for
all pairs. The chart retains the origin and preserves all orientation bits. -/
theorem finite_anchor_chart {n : ℕ} (p : Fin (n+1) → Plane)
    (h0 : p 0 = (0,0))
    (hx : ∀ i, 0 < i → 0 < (p i).1)
    (hs : ∀ i j, 0 < i → i < j → (p i).2/(p i).1 < (p j).2/(p j).1) :
    ∃ e C : ℝ, 0 < e ∧ StrictMono (fun i => (anchorChart e C (p i)).1) ∧
      (∀ i j k, positiveBit (orient (anchorChart e C (p i)) (anchorChart e C (p j))
        (anchorChart e C (p k))) = positiveBit (orient (p i) (p j) (p k))) ∧
      (∀ i j, 0 < i → i < j → 0 < orient (anchorChart e C (p 0))
        (anchorChart e C (p i)) (anchorChart e C (p j))) := by
  classical
  let B := Finset.univ.image (fun i => -((p i).2/(p i).1))
  let H := insert (0 : ℝ) B
  have hH : H.Nonempty := ⟨0, by simp [H]⟩
  let C := H.max' hH + 1
  have hnum (i : Fin (n+1)) (hi : 0 < i) : 0 < (p i).2 + C*(p i).1 := by
    have hmem : -((p i).2/(p i).1) ∈ H :=
      Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    have hle := H.le_max' _ hmem
    have hlt : -((p i).2/(p i).1) < C := hle.trans_lt (lt_add_of_pos_right _ zero_lt_one)
    have hann : -(p i).2 < C * (p i).1 := by
      rw [← neg_div] at hlt
      exact (div_lt_iff₀ (hx i hi)).mp hlt
    linarith
  let pairs : Finset (Fin (n+1) × Fin (n+1)) :=
    Finset.univ.filter (fun ij => 0 < ij.1 ∧ ij.1 < ij.2)
  let bound := fun ij : Fin (n+1) × Fin (n+1) =>
    ((p ij.2).2*(p ij.1).1 - (p ij.1).2*(p ij.2).1) /
      (|(p ij.2).2 + C*(p ij.2).1 - ((p ij.1).2 + C*(p ij.1).1)| + 1)
  let bounds := insert (1 : ℝ) (pairs.image bound)
  have hn : bounds.Nonempty := ⟨1, by simp [bounds]⟩
  have hb (x) (h : x ∈ bounds) : 0 < x := by
    rcases Finset.mem_insert.mp h with rfl | h
    · exact zero_lt_one
    obtain ⟨⟨i,j⟩, hij, rfl⟩ := Finset.mem_image.mp h
    obtain ⟨hi,hij⟩ := (Finset.mem_filter.mp hij).2
    have hj := hi.trans hij
    apply div_pos
    · have hh := (div_lt_div_iff₀ (hx i hi) (hx j hj)).mp (hs i j hi hij)
      nlinarith
    · positivity
  let e := bounds.min' hn / 2
  have hmin : 0 < bounds.min' hn := hb _ (Finset.min'_mem _ _)
  have he : 0 < e := by dsimp [e]; positivity
  have hcoord (i : Fin (n+1)) : 0 ≤ (p i).1 := by
    by_cases hi : 0 < i
    · exact (hx i hi).le
    · have hzi : i = 0 := le_antisymm (le_of_not_gt hi) (Fin.zero_le i)
      simp [hzi,h0]
  have hd (i : Fin (n+1)) : 0 < (p i).1+e := add_pos_of_nonneg_of_pos (hcoord i) he
  refine ⟨e,C,he,?_,?_,?_⟩
  · intro i j hij
    by_cases hi : 0 < i
    · have hj := hi.trans hij
      have hmem : bound (i,j) ∈ bounds := Finset.mem_insert_of_mem
        (Finset.mem_image.mpr ⟨(i,j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi, hij⟩, rfl⟩)
      have hsmall : e < bound (i,j) := (show e < bounds.min' hn by dsimp [e]; linarith).trans_le
        (Finset.min'_le bounds _ hmem)
      have hpos : 0 < |(p j).2 + C*(p j).1 - ((p i).2 + C*(p i).1)| + 1 :=
        add_pos_of_nonneg_of_pos (abs_nonneg _) zero_lt_one
      apply anchor_x_lt_of_small he (hx i hi) (hx j hj) (hs i j hi hij)
      exact (lt_div_iff₀ hpos).mp hsmall
    · have hzi : i = 0 := le_antisymm (le_of_not_gt hi) (Fin.zero_le i)
      subst i
      change (anchorChart e C (p 0)).1 < (anchorChart e C (p j)).1
      rw [h0,anchorChart_zero]
      exact div_pos (hnum j hij) (hd j)
  · intro i j k
    exact positiveBit_orient_anchorChart e C (p i) (p j) (p k) he (hd i) (hd j) (hd k)
  · intro i j hi hij
    have hor : 0 < orient (p 0) (p i) (p j) := by
      rw [h0]
      exact (orient_origin_pos_iff_slope (p i) (p j) (hx i hi) (hx j (hi.trans hij))).2
        (hs i j hi hij)
    have ht := orient_anchorChart_mul e C (p 0) (p i) (p j)
      (hd 0).ne' (hd i).ne' (hd j).ne'
    exact (mul_pos_iff_of_pos_right (mul_pos (mul_pos (hd 0) (hd i)) (hd j))).mp
      (ht.symm ▸ mul_pos he hor)

/-- Translating the chosen point to the origin preserves all orientations. -/
def moveOrigin (a b : Plane) : Plane := (b.1-a.1,b.2-a.2)

@[simp] theorem orient_moveOrigin (o a b c : Plane) :
    orient (moveOrigin o a) (moveOrigin o b) (moveOrigin o c) = orient a b c := by
  simp only [moveOrigin, orient]
  ring

/-- Once points are x-sorted, angular sorting fixes the leftmost point and
orders all other points by slope after translation to the origin. -/
theorem exists_angular_order {n : ℕ} (p : Fin (n+1) ↪ Plane)
    (hp : StrictMono (fun i => (p i).1)) (gp : GeneralPositionAll p) :
    ∃ f : Fin (n+1) ↪ Fin (n+1), f 0 = 0 ∧
      ∀ i j, 0 < i → i < j →
        (moveOrigin (p 0) (p (f i))).2/(moveOrigin (p 0) (p (f i))).1 <
          (moveOrigin (p 0) (p (f j))).2/(moveOrigin (p 0) (p (f j))).1 := by
  classical
  let r := fun i => moveOrigin (p 0) (p i)
  let s := fun i => (r i).2/(r i).1
  have rx (i) (hi : i ≠ 0) : 0 < (r i).1 :=
    sub_pos.mpr (hp (lt_of_le_of_ne (Fin.zero_le i) hi.symm))
  have sij (i j) (hi : i ≠ 0) (hj : j ≠ 0) (he : s i = s j) : i = j := by
    by_contra hne
    have hor := gp 0 i j hi.symm hj.symm hne
    have hzero : r 0 = (0,0) := by simp [r,moveOrigin]
    have hsame : orient (r 0) (r i) (r j) = 0 := by
      rw [hzero]
      have hh := (div_eq_div_iff (rx i hi).ne' (rx j hj).ne').mp he
      change (r i).2 * (r j).1 = (r j).2 * (r i).1 at hh
      simp only [orient, sub_zero]
      nlinarith
    have eq := orient_moveOrigin (p 0) (p 0) (p i) (p j)
    exact hor (eq.symm.trans hsame)
  let D := Finset.univ.image s
  have hn : D.Nonempty := ⟨s 0,Finset.mem_image.mpr ⟨0,Finset.mem_univ _,rfl⟩⟩
  let lo := D.min' hn - 1
  have hlo (i) : lo < s i := (sub_lt_self _ zero_lt_one).trans_le
    (Finset.min'_le D (s i) (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩))
  let key := fun i => if i = 0 then lo else s i
  have hinj : Function.Injective key := by
    intro i j h
    by_cases hi : i = 0
    · by_cases hj : j = 0
      · exact hi.trans hj.symm
      · have he : lo = s j := by simpa [key,hi,hj] using h
        exact ((hlo j).ne he).elim
    · by_cases hj : j = 0
      · have he : s i = lo := by simpa [key,hi,hj] using h
        exact ((hlo i).ne he.symm).elim
      · exact sij i j hi hj (by simpa [key,hi,hj] using h)
  obtain ⟨f,hf⟩ := exists_key_order key hinj
  have fsurj : Function.Surjective f := Finite.surjective_of_injective f.injective
  have hf0 : f 0 = 0 := by
    obtain ⟨i,hi⟩ := fsurj 0
    by_cases hz : i = 0
    · simpa [hz] using hi
    · have hi0 : 0 < i := lt_of_le_of_ne (Fin.zero_le _) (fun h => hz h.symm)
      have he := hf hi0
      change key (f 0) < key (f i) at he
      have hne : f 0 ≠ 0 := by
        intro hbad
        exact hz (f.injective (hi.trans hbad.symm))
      simp only [key, hi, hne, ↓reduceIte] at he
      exact ((hlo (f 0)).not_gt he).elim
  refine ⟨f,hf0,?_⟩
  intro i j hi hij
  have hne (a : Fin (n+1)) (ha : 0 < a) : f a ≠ 0 :=
    fun h => ha.ne' (f.injective (h.trans hf0.symm))
  have hlt := hf hij
  change key (f i) < key (f j) at hlt
  simpa only [key, hne i hi, hne j (hi.trans hij), ↓reduceIte] using hlt

/-- The finite anchor is available on an arbitrary finite general-position
configuration. It preserves the signs on every triple up to reindexing,
and its new leftmost point has positive orientation on each later pair. -/
theorem positive_anchor_exists {n : ℕ} (p : Fin (n+1) ↪ Plane) (gp : GeneralPositionAll p) :
    ∃ (f : Fin (n+1) ↪ Fin (n+1)) (q : Fin (n+1) → Plane),
      StrictMono (fun i => (q i).1) ∧
      (∀ i j k, positiveBit (orient (q i) (q j) (q k)) =
        positiveBit (orient (p (f i)) (p (f j)) (p (f k)))) ∧
      (∀ i j, 0 < i → i < j → 0 < orient (q 0) (q i) (q j)) := by
  obtain ⟨t,ht⟩ := exists_injective_shear_key p
  obtain ⟨f,hf⟩ := exists_key_order (fun i => (shear t (p i)).1) ht
  let pp : Fin (n+1) ↪ Plane := ⟨fun i => shear t (p (f i)), fun i j h =>
    hf.injective (congrArg Prod.fst h)⟩
  have hgp : GeneralPositionAll pp := by
    intro i j k hij hik hjk
    change orient (shear t (p (f i))) (shear t (p (f j))) (shear t (p (f k))) ≠ 0
    rw [orient_shear]
    exact gp _ _ _ (f.injective.ne hij) (f.injective.ne hik) (f.injective.ne hjk)
  obtain ⟨g,hg0,hg⟩ := exists_angular_order pp hf hgp
  let r := fun i => moveOrigin (pp 0) (pp (g i))
  have hr0 : r 0 = (0,0) := by simp [r,hg0,moveOrigin]
  have hrx (i) (hi : 0 < i) : 0 < (r i).1 := by
    have hne : g i ≠ 0 := fun hh => hi.ne' (g.injective (hh.trans hg0.symm))
    exact sub_pos.mpr (hf (lt_of_le_of_ne (Fin.zero_le _) hne.symm))
  obtain ⟨e,C,_he,hord,hsigns,hanchor⟩ := finite_anchor_chart r hr0 hrx hg
  refine ⟨g.trans f, fun i => anchorChart e C (r i), hord, ?_, hanchor⟩
  intro i j k
  rw [hsigns]
  change positiveBit (orient (moveOrigin (pp 0) (pp (g i)))
    (moveOrigin (pp 0) (pp (g j))) (moveOrigin (pp 0) (pp (g k)))) = _
  rw [orient_moveOrigin]
  exact congrArg positiveBit (orient_shear t _ _ _)

/-- A geometric counterexample has an avoidance signotope with positive
leftmost anchor. This lemma does not assert the residual CNF is UNSAT. -/
theorem geometric_counterexample_gives_positive_anchor {n : ℕ}
    (p : Fin (n+1) ↪ Plane) (gp : GeneralPositionAll p)
    (h : ¬ ∃ s : Finset Plane, s ⊆ Finset.univ.map p ∧ s.card = 7 ∧ ConvexPosition s) :
    ∃ χ : Fin (n+1) → Fin (n+1) → Fin (n+1) → Bool,
      SignotopeConstraints (n+1) χ ∧ AvoidanceClauses (n+1) χ ∧
      (∀ i j, 0 < i → i < j → χ 0 i j = true) := by
  classical
  obtain ⟨f,q,hq,hsgn,ha⟩ := positive_anchor_exists p gp
  let χ := orientations (f.trans p)
  have hsign (i j k : Fin (n+1)) :
      positiveBit (orient (q i) (q j) (q k)) = χ i j k := hsgn i j k
  refine ⟨χ, ?_, ?_, ?_⟩
  · intro i j k l hij hjk hkl
    simpa only [hsign] using ordered_quad_signotope (q i) (q j) (q k) (q l)
      (hq hij) (hq hjk) (hq hkl)
  · have gp' : GeneralPosition (f.trans p) := by
      intro i j k hij hjk
      exact gp _ _ _ (f.injective.ne hij.ne) (f.injective.ne (hij.trans hjk).ne)
        (f.injective.ne hjk.ne)
    apply (no_heptagon_iff_orientation_clauses (f.trans p) gp').mp
    rintro ⟨s,hs,hcard,hconv⟩
    apply h
    refine ⟨s,hs.trans ?_,hcard,hconv⟩
    intro x hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hx
    exact Finset.mem_map.mpr ⟨f i,Finset.mem_univ _,rfl⟩
  · intro i j hi hij
    rw [← hsign]
    simpa only [positiveBit, decide_eq_true_eq] using ha i j hi hij

#print axioms geometric_counterexample_gives_positive_anchor
#print axioms exists_angular_order
#print axioms positive_anchor_exists
#print axioms finite_anchor_chart
#print axioms orient_anchorChart_mul
#print axioms orient_anchorChart_ne
#print axioms positiveBit_orient_anchorChart
#print axioms orient_origin_pos_iff_slope
#print axioms anchor_x_lt_of_small

end ES33

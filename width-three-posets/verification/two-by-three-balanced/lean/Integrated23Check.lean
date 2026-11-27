import TwoByThreeMajority
import BranchOrder
import Mathlib.Basic.Finite.Sigma
import Mathlib.Tactic.FinCases


namespace WidthThree
open TwoByThreeReplay

section
variable {α : Type*} [PartialOrder α] [Fintype α] {n : ℕ}

/-- Exactly b plus the two- and three-element ordered arms in the branch. -/
structure TwoByThreeShape (v : Fin 7 → α) : Prop where
  inj : Function.Injective v
  lower_x : v 0 < v 1
  lower_y : v 0 < v 3
  rail1 : v 1 < v 2
  rail2 : v 3 < v 4
  rail3 : v 4 < v 5
  branch : ∀ z, Branch (v 6) (v 0) z ↔ ∃ u : Fin 7, u ≠ 6 ∧ v u = z

private def tag23 (r : Fin 7 → ℕ) : Fin 10 :=
  if r 1 < r 3 then
    if r 2 < r 3 then 0
    else if r 2 < r 4 then 1
    else if r 2 < r 5 then 2 else 3
  else if r 1 < r 4 then
    if r 2 < r 4 then 4
    else if r 2 < r 5 then 5 else 6
  else if r 1 < r 5 then
    if r 2 < r 5 then 7 else 8
  else 9

set_option maxHeartbeats 1600000 in
private theorem tag23_classifies (r : Fin 7 → ℕ) (hinj : Function.Injective r)
    (h01 : r 0 < r 1) (h03 : r 0 < r 3) (h12 : r 1 < r 2) (h34 : r 3 < r 4)
    (h45 : r 4 < r 5) (i j : Fin 7) (hi : i ≠ 6) (hj : j ≠ 6) :
    r i < r j ↔ branchRank (tag23 r) i < branchRank (tag23 r) j := by
  have h13 : r 1 ≠ r 3 := fun h => (by decide : (1 : Fin 7) ≠ 3) (hinj h)
  have h23 : r 2 ≠ r 3 := fun h => (by decide : (2 : Fin 7) ≠ 3) (hinj h)
  have h14 : r 1 ≠ r 4 := fun h => (by decide : (1 : Fin 7) ≠ 4) (hinj h)
  have h24 : r 2 ≠ r 4 := fun h => (by decide : (2 : Fin 7) ≠ 4) (hinj h)
  have h15 : r 1 ≠ r 5 := fun h => (by decide : (1 : Fin 7) ≠ 5) (hinj h)
  have h25 : r 2 ≠ r 5 := fun h => (by decide : (2 : Fin 7) ≠ 5) (hinj h)
  unfold tag23
  repeat' split
  all_goals fin_cases i <;> fin_cases j <;> simp [branchRank] at * <;> omega

private theorem table_filter_card :
    ∀ (p : Fin 10) (i : Fin 7), i ≠ 6 →
      (Finset.univ.filter fun j => j ≠ 6 ∧ branchRank p j < branchRank p i).card =
        branchRank p i := by decide

private theorem table_filter_card_le :
    ∀ (p : Fin 10) (i : Fin 7), i ≠ 6 →
      (Finset.univ.filter fun j => j ≠ 6 ∧ branchRank p j ≤ branchRank p i).card =
        branchRank p i + 1 := by decide

private theorem tag23_invariant (v : Fin 7 → α) (H : TwoByThreeShape v) (p : Fin 10) :
    BranchOrderInvariant (v 6) (v 0) (fun R : Ranking α n =>
      tag23 (fun i => (R.rank (v i)).val) = p) := by
  intro R T rel h
  have b (i : Fin 7) (hi : i ≠ 6) : Branch (v 6) (v 0) (v i) :=
    (H.branch _).mpr ⟨i, hi, rfl⟩
  have eq (i j : Fin 7) (hi : i ≠ 6) (hj : j ≠ 6) :
      (R.rank (v i)).val < (R.rank (v j)).val ↔ (T.rank (v i)).val < (T.rank (v j)).val :=
    rel _ _ (b i hi) (b j hj)
  unfold tag23 at h ⊢
  simp only [← eq 1 3 (by decide) (by decide), ← eq 2 3 (by decide) (by decide),
    ← eq 1 4 (by decide) (by decide), ← eq 2 4 (by decide) (by decide),
    ← eq 1 5 (by decide) (by decide), ← eq 2 5 (by decide) (by decide)]
  exact h

private theorem beforeSet_card_le_six (v : Fin 7 → α) (H : TwoByThreeShape v) (R : Ranking α n) :
    (beforeSet R (v 6) (Branch (v 6) (v 0))).card < 7 := by
  classical
  let D : Finset (Fin 7) := Finset.univ.erase 6
  have hD : D.card = 6 := by decide
  have hs : beforeSet R (v 6) (Branch (v 6) (v 0)) ⊆ D.image v := by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := (H.branch z).mp (mem_beforeSet.mp hz).1
    exact Finset.mem_image.mpr ⟨i, by simp [D,hi], rfl⟩
  have hc := (Finset.card_le_card hs).trans Finset.card_image_le
  omega

private theorem twoByThree_rank_representation (v : Fin 7 → α) (H : TwoByThreeShape v)
    (R : Ranking α n) (i j : Fin 7) :
    R.rank (v i) < R.rank (v j) ↔
      TwoByThreeReplay.rank (tag23 (fun z => (R.rank (v z)).val)) ⟨_, beforeSet_card_le_six v H R⟩ i <
      TwoByThreeReplay.rank (tag23 (fun z => (R.rank (v z)).val)) ⟨_, beforeSet_card_le_six v H R⟩ j := by
  classical
  let r := fun z => (R.rank (v z)).val
  let p := tag23 r
  let B := beforeSet R (v 6) (Branch (v 6) (v 0))
  let k := B.card
  have hinj : Function.Injective r := fun _ _ e => H.inj (R.inj (Fin.ext e))
  have hh (u w : Fin 7) (hu : u ≠ 6) (hw : w ≠ 6) :
      r u < r w ↔ branchRank p u < branchRank p w :=
    tag23_classifies r hinj (R.mono H.lower_x) (R.mono H.lower_y) (R.mono H.rail1)
      (R.mono H.rail2) (R.mono H.rail3) u w hu hw
  have cut (u : Fin 7) (hu : u ≠ 6) :
      r 6 < r u ↔ k ≤ branchRank p u := by
    constructor
    · intro h
      let I := Finset.univ.filter fun z : Fin 7 => z ≠ 6 ∧ branchRank p z < branchRank p u
      have hsub : B ⊆ I.image v := by
        intro z hz
        obtain ⟨hzB, hzLt⟩ := mem_beforeSet.mp hz
        obtain ⟨w, hw, rfl⟩ := (H.branch z).mp hzB
        have hzR : r w < r 6 := hzLt
        have hm := (hh w u hw hu).mp (hzR.trans h)
        exact Finset.mem_image.mpr ⟨w, by simp [I, hw, hm], rfl⟩
      exact (Finset.card_le_card hsub).trans
        (Finset.card_image_le.trans_eq (table_filter_card p u hu))
    · intro h
      by_contra! hn
      have hult : r u < r 6 := lt_of_le_of_ne hn (fun e => hu (hinj e))
      let I := Finset.univ.filter fun z : Fin 7 => z ≠ 6 ∧ branchRank p z ≤ branchRank p u
      have hsub : I.image v ⊆ B := by
        intro z hz
        obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
        have hm : w ≠ 6 ∧ branchRank p w ≤ branchRank p u := by simpa [I] using hw
        have hwB := (H.branch _).mpr ⟨w, hm.1, rfl⟩
        have hle : r w ≤ r u := by
          apply le_of_not_gt
          intro hgt
          exact (not_lt_of_ge hm.2) ((hh u w hu hm.1).mp hgt)
        exact mem_beforeSet.mpr ⟨hwB, lt_of_le_of_lt hle hult⟩
      have hc := Finset.card_le_card hsub
      rw [Finset.card_image_of_injective _ H.inj, table_filter_card_le p u hu] at hc
      change branchRank p u + 1 ≤ k at hc
      omega
  change r i < r j ↔ TwoByThreeReplay.rank p ⟨k, _⟩ i < TwoByThreeReplay.rank p ⟨k, _⟩ j
  by_cases hi : i = 6
  · subst i
    by_cases hj : j = 6
    · subst j; simp
    · have hc := cut j hj
      simp only [TwoByThreeReplay.rank, ite_true, ite_eq_right hj]
      by_cases h : k ≤ branchRank p j <;> simp only [h, ite_true, ite_false] <;> omega
  · by_cases hj : j = 6
    · subst j
      have hc := cut i hi
      have hne : r i ≠ r 6 := fun e => hi (hinj e)
      simp only [TwoByThreeReplay.rank, ite_true, ite_eq_right hi]
      by_cases h : k ≤ branchRank p i <;> simp only [h, ite_true, ite_false] <;> omega
    · have hc := hh i j hi hj
      simp only [TwoByThreeReplay.rank, ite_eq_right hi, ite_eq_right hj]
      split <;> split <;> omega


/-- Every ranking of a six-vertex 2×3 branch is classified by an interleaving
and a cut. The classification order is invariant under branch-order swaps. -/
theorem exists_twoByThree_classification (v : Fin 7 → α) (H : TwoByThreeShape v) :
    ∃ (f : Ranking α n → Fin 10)
      (bound : ∀ R : Ranking α n, (beforeSet R (v 6) (Branch (v 6) (v 0))).card < 7),
      (∀ p, BranchOrderInvariant (v 6) (v 0) (fun R => f R = p)) ∧
      (∀ (R : Ranking α n) (i j : Fin 7),
        R.rank (v i) < R.rank (v j) ↔
          TwoByThreeReplay.rank (f R) ⟨_,bound R⟩ i < TwoByThreeReplay.rank (f R) ⟨_,bound R⟩ j) ∧
      (∀ (R : Ranking α n), R.rank (v 1) < R.rank (v 5) ↔ branchRank (f R) 1 < branchRank (f R) 5) := by
  refine ⟨fun R => tag23 (fun z => (R.rank (v z)).val), beforeSet_card_le_six v H,
    tag23_invariant v H, twoByThree_rank_representation v H, ?_⟩
  intro R
  let r := fun z => (R.rank (v z)).val
  have hinj : Function.Injective r := fun _ _ e => H.inj (R.inj (Fin.ext e))
  exact tag23_classifies r hinj (R.mono H.lower_x) (R.mono H.lower_y)
    (R.mono H.rail1) (R.mono H.rail2) (R.mono H.rail3) 1 5 (by decide) (by decide)

#print axioms exists_twoByThree_classification
end
end WidthThree

namespace WidthThree
open TwoByThreeReplay
private noncomputable abbrev countEvent {γ : Type*} (E : γ → Prop) := Nat.card {r : γ // E r}

/-- A finite partition of a counted event into ten-by-seven key fibers. -/
private theorem card_partition {γ : Type*} [Finite γ] (E : γ → Prop)
    (f : γ → Fin 10) (g : γ → Fin 7) :
    countEvent E = ∑ p : Fin 10, ∑ j : Fin 7, countEvent
      (fun r => f r = p ∧ g r = j ∧ E r) := by
  let S := Σ p : Fin 10, Σ j : Fin 7, {r : γ // f r = p ∧ g r = j ∧ E r}
  let equiv : {r : γ // E r} ≃ S :=
    { toFun := fun r => ⟨f r.val, g r.val, r.val, rfl, rfl, r.property⟩
      invFun := fun s => ⟨s.2.2.val, s.2.2.property.2.2⟩
      left_inv := fun _ => rfl
      right_inv := by
        rintro ⟨p,j,r,hp,hj,hr⟩
        subst p
        subst j
        rfl }
  unfold countEvent
  rw [Nat.card_congr equiv]
  simp only [S, Nat.card_sigma]


section
variable {α : Type*} [PartialOrder α] [Fintype α] {n : ℕ}

def binMass23 (q : Fin 10 → Fin 7 → ℕ) : ℕ := ∑ p : Fin 10, ∑ j : Fin 7, q p j

def binCount23 (q : Fin 10 → Fin 7 → ℕ) (u v : Fin 7) : ℕ :=
  ∑ p : Fin 10, ∑ j : Fin 7, if TwoByThreeReplay.rank p j u < TwoByThreeReplay.rank p j v then q p j else 0

private noncomputable abbrev branchPairCount (u v : α) (n : ℕ) : ℕ :=
  Nat.card {R : Ranking α n // R.rank u < R.rank v}

/-- Actual rankings realize an antitone histogram with exactly the tabulated
pair counts, and the x<Z assumption cuts the classified support as desired. -/
theorem twoByThree_rankings_have_histogram (v : Fin 7 → α) (H : TwoByThreeShape v)
    (hba : ¬ v 0 ≤ v 6) (hd : ∀ z, z < v 6 → z < v 0) :
    ∃ q : Fin 10 → Fin 7 → ℕ,
      (∀ p, Antitone (q p)) ∧
      Nat.card (Ranking α n) = binMass23 q ∧
      (∀ u w : Fin 7, branchPairCount (v u) (v w) n = binCount23 q u w) ∧
      (v 1 < v 5 → ∀ p j, ¬branchRank p 1 < branchRank p 5 → q p j = 0) := by
  classical
  obtain ⟨f,bound,hinv,hrel,hsupp⟩ := exists_twoByThree_classification (n := n) v H
  let a := v 6
  let b := v 0
  let g (R : Ranking α n) : Fin 7 := ⟨(beforeSet R a (Branch a b)).card, bound R⟩
  let q (p : Fin 10) (j : Fin 7) := countEvent (fun R : Ranking α n => f R = p ∧ g R = j)
  have cardBin (p : Fin 10) (j : Fin 7) : q p j = Nat.card (BinGiven a b j.val (fun R => f R = p)) := by
    apply Nat.card_congr
    apply Equiv.subtypeEquivProp
    funext R
    apply propext
    change (f R = p ∧ g R = j) ↔ (g R).val = j.val ∧ f R = p
    rw [Fin.val_inj]
    exact and_comm
  have hq (p : Fin 10) : Antitone (q p) := by
    have hq' : Antitone (fun i => Nat.card (BinGiven a b i (fun R => f R = p))) :=
      antitone_nat_of_succ_le (fun i => natCard_binGiven_succ_le a b hba hd i _ (hinv p))
    intro j k hjk
    rw [cardBin, cardBin]
    exact hq' hjk
  have mEq : Nat.card (Ranking α n) = binMass23 q := by
    have he := card_partition (fun _ : Ranking α n => True) f g
    rw [← Nat.card_congr (Equiv.subtypeUnivEquiv (p := fun _ : Ranking α n => True) (fun _ => trivial))]
    simpa [binMass23, q] using he
  have cEq (u w : Fin 7) : branchPairCount (v u) (v w) n = binCount23 q u w := by
    unfold binCount23
    change countEvent (fun R : Ranking α n => R.rank (v u) < R.rank (v w)) = _
    rw [card_partition (fun R : Ranking α n => R.rank (v u) < R.rank (v w)) f g]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro j _
    by_cases hp : TwoByThreeReplay.rank p j u < TwoByThreeReplay.rank p j w
    · rw [ite_eq_left hp]
      apply Nat.card_congr
      apply Equiv.subtypeEquivProp
      funext R
      apply propext
      change (f R = p ∧ g R = j ∧ _) ↔ f R = p ∧ g R = j
      constructor
      · exact fun h => ⟨h.1,h.2.1⟩
      · intro h
        refine ⟨h.1,h.2,(hrel R u w).mpr ?_⟩
        change TwoByThreeReplay.rank (f R) (g R) u < TwoByThreeReplay.rank (f R) (g R) w
        simpa only [h.1,h.2] using hp
    · rw [ite_eq_right hp]
      apply Nat.card_eq_zero.mpr
      left
      refine ⟨fun ⟨R, h₁,h₂,h₃⟩ => hp ?_⟩
      have hh := (hrel R u w).mp h₃
      change TwoByThreeReplay.rank (f R) (g R) u < TwoByThreeReplay.rank (f R) (g R) w at hh
      simpa only [h₁,h₂] using hh

  refine ⟨q,hq,mEq,cEq,?_⟩
  intro hx p j hb
  apply Nat.card_eq_zero.mpr
  left
  refine ⟨fun R => hb ?_⟩
  have hxZ : R.val.rank (v 1) < R.val.rank (v 5) := R.val.mono hx
  simpa only [R.property.1] using (hsupp R.val).mp hxZ

#print axioms twoByThree_rankings_have_histogram
end
end WidthThree


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


namespace WidthThree

open TwoByThreeReplay

noncomputable section

variable {α : Type*} [PartialOrder α] [Fintype α] {n : ℕ}

private abbrev c23 (x y : α) (n : ℕ) :=
  Nat.card {R : Ranking α n // R.rank x < R.rank y}

/-- For the exclusive-upset shape consisting of the root and two ordered arms
of lengths 2 and 3, the usual predecessor-set hypothesis and a root-first
probability of at most 7/30 guarantee a balanced comparison. The threshold
improves to 1/4 if x is below Z in the poset. The theorem does not require
other cross-arm comparisons to be absent. -/
theorem balanced_of_twoByThreeShape (v : Fin 7 → α) (H : TwoByThreeShape v)
    (hba : ¬ v 0 ≤ v 6) (hd : ∀ z, z < v 6 → z < v 0)
    (cap : (30 * c23 (v 6) (v 0) n ≤ 7 * Nat.card (Ranking α n)) ∨
      (v 1 < v 5 ∧ 4 * c23 (v 6) (v 0) n ≤ Nat.card (Ranking α n))) :
    ∃ x y : α, x ≠ y ∧ Nat.card (Ranking α n) ≤ 3 * c23 x y n ∧
      3 * c23 x y n ≤ 2 * Nat.card (Ranking α n) := by
  obtain ⟨q,hq,hM,hC,hsupp⟩ := twoByThree_rankings_have_histogram (n:=n) v H hba hd
  let w := toCutoffWeights q
  have mEq : modelMass w = Nat.card (Ranking α n) :=
    (weightedMass_eq q hq).trans hM.symm
  have cEq (u z : Fin 7) : modelCount w u z = c23 (v u) (v z) n :=
    (weightedCount_eq q hq u z).trans (hC u z).symm
  have cap' : (30 * modelCount w 6 0 ≤ 7 * modelMass w) ∨
      (v 1 < v 5 ∧ 4 * modelCount w 6 0 ≤ modelMass w) := by
    simpa only [cEq,mEq] using cap
  have hbal : HasBalanced w := by
    by_contra hn
    have hhalf : 2 * modelCount w 6 0 ≤ modelMass w := by
      rcases cap' with h | ⟨_,h⟩ <;> omega
    obtain ⟨p,j,h⟩ := exists_classified_strong_order w hn hhalf
    have strong (u z : Fin 7) (ho : rank p j.succ u < rank p j.succ z) :
        2 * mass w < 3 * count w u z :=
      (h u z).mpr ho
    rcases cap' with c | ⟨hXZ,c⟩
    · exact no_strong_majority_7_30 w p j c strong
    · have support (p : Fin 10) (k : Fin 7) (hnp : ¬ branchRank p 1 < branchRank p 5) : w p k = 0 :=
        toCutoffWeights_zero q p (fun j => hsupp hXZ p j hnp) k
      exact no_strong_majority_quarter_of_x_before_Z w p j support c strong
  obtain ⟨u,z,hne,hlo,hhi⟩ := hbal
  exact ⟨v u, v z, (fun e => hne (H.inj e)), by simpa only [mEq,cEq] using hlo,
    by simpa only [mEq,cEq] using hhi⟩

end

#print axioms balanced_of_twoByThreeShape
end WidthThree

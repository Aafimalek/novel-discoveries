import TwoArmsBins
import Mathlib.Data.Finite.Sigma
import BranchOrder
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FinCases

namespace WidthThree
open TwoArmsMix

private noncomputable abbrev countEvent {γ : Type*} (E : γ → Prop) := Nat.card {r : γ // E r}

/-- A finite partition of a counted event into six-by-six key fibers. -/
private theorem card_partition {γ : Type*} [Finite γ] (E : γ → Prop)
    (f g : γ → Fin 6) :
    countEvent E = ∑ p : Fin 6, ∑ j : Fin 6, countEvent
      (fun r => f r = p ∧ g r = j ∧ E r) := by
  let S := Σ p : Fin 6, Σ j : Fin 6, {r : γ // f r = p ∧ g r = j ∧ E r}
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

section Balancing
variable {α : Type*} [PartialOrder α] [Fintype α] {n : ℕ}

private noncomputable abbrev pairCount (x y : α) (n : ℕ) : ℕ :=
  Nat.card {R : Ranking α n // R.rank x < R.rank y}
private abbrev Balanced (x y : α) (n : ℕ) : Prop :=
  x ≠ y ∧ Nat.card (Ranking α n) ≤ 3 * pairCount x y n ∧
    3 * pairCount x y n ≤ 2 * Nat.card (Ranking α n)

/-- Once six branch orders classify the rankings and identify all pair
comparisons through their cut, the numerical quarter bound applies verbatim. -/
theorem balanced_of_twoArmClassification (v : Fin 6 → α) (hv : Function.Injective v)
    (hba : ¬ v 0 ≤ v 5) (hd : ∀ z, z < v 5 → z < v 0)
    (f : Ranking α n → Fin 6)
    (hinv : ∀ p, BranchOrderInvariant (v 5) (v 0) fun R => f R = p)
    (hsize : ∀ R : Ranking α n, (beforeSet R (v 5) (Branch (v 5) (v 0))).card < 6)
    (hrel : ∀ (R : Ranking α n) (u w : Fin 6),
      R.rank (v u) < R.rank (v w) ↔
        TwoArmsMix.rank (f R) ⟨_, hsize R⟩ u < TwoArmsMix.rank (f R) ⟨_, hsize R⟩ w)
    (hcap : 4 * pairCount (v 5) (v 0) n ≤ Nat.card (Ranking α n)) :
    ∃ x y : α, Balanced x y n := by
  classical
  let a := v 5
  let b := v 0
  let g (R : Ranking α n) : Fin 6 := ⟨(beforeSet R a (Branch a b)).card, hsize R⟩
  let q (p j : Fin 6) := countEvent (fun R : Ranking α n => f R = p ∧ g R = j)
  have cardBin (p j : Fin 6) : q p j = Nat.card (BinGiven a b j.val (fun R => f R = p)) := by
    apply Nat.card_congr
    apply Equiv.subtypeEquivProp
    funext R
    apply propext
    change (f R = p ∧ g R = j) ↔ (g R).val = j.val ∧ f R = p
    rw [Fin.val_inj]
    exact and_comm
  have hq (p : Fin 6) : Antitone (q p) := by
    have hq' : Antitone (fun i => Nat.card (BinGiven a b i (fun R => f R = p))) :=
      antitone_nat_of_succ_le (fun i => natCard_binGiven_succ_le a b hba hd i _ (hinv p))
    intro j k hjk
    rw [cardBin, cardBin]
    exact hq' hjk
  have mEq : Nat.card (Ranking α n) = binMass q := by
    have he := card_partition (fun _ : Ranking α n => True) f g
    rw [← Nat.card_congr (Equiv.subtypeUnivEquiv (p := fun _ : Ranking α n => True) (fun _ => trivial))]
    simpa [binMass, q] using he
  have cEq (u w : Fin 6) : pairCount (v u) (v w) n = binCount q u w := by
    unfold binCount
    change countEvent (fun R : Ranking α n => R.rank (v u) < R.rank (v w)) = _
    rw [card_partition (fun R : Ranking α n => R.rank (v u) < R.rank (v w)) f g]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro j _
    by_cases hp : TwoArmsMix.rank p j u < TwoArmsMix.rank p j w
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
        change TwoArmsMix.rank (f R) (g R) u < TwoArmsMix.rank (f R) (g R) w
        simpa only [h.1,h.2] using hp
    · rw [ite_eq_right hp]
      apply Nat.card_eq_zero.mpr
      left
      refine ⟨fun ⟨R, h₁,h₂,h₃⟩ => hp ?_⟩
      have hh := (hrel R u w).mp h₃
      change TwoArmsMix.rank (f R) (g R) u < TwoArmsMix.rank (f R) (g R) w at hh
      simpa only [h₁,h₂] using hh
  have cap : 4 * binCount q 5 0 ≤ binMass q := by simpa only [← mEq, ← cEq] using hcap
  obtain ⟨u,w, hne, hlow, hhigh⟩ := balanced_quarter_bins q hq cap
  exact ⟨v u, v w, (fun e => hne (hv e)), by simpa only [mEq,cEq] using hlow,
    by simpa only [mEq,cEq] using hhigh⟩


/-- Finite order geometry for the two two-element arms. Comparisons between
arms may be additionally constrained by the ambient poset. -/
structure TwoArmShape (v : Fin 6 → α) : Prop where
  inj : Function.Injective v
  lower_x : v 0 < v 1
  lower_y : v 0 < v 3
  rail1 : v 1 < v 2
  rail2 : v 3 < v 4
  branch : ∀ z, Branch (v 5) (v 0) z ↔ ∃ u : Fin 6, u ≠ 5 ∧ v u = z

private def tag (r : Fin 6 → ℕ) : Fin 6 :=
  if r 1 < r 3 then
    if r 2 < r 3 then 0 else if r 2 < r 4 then 1 else 2
  else
    if r 4 < r 1 then 5 else if r 4 < r 2 then 4 else 3

private theorem tag_classifies (r : Fin 6 → ℕ) (hinj : Function.Injective r)
    (h01 : r 0 < r 1) (h03 : r 0 < r 3) (h12 : r 1 < r 2) (h34 : r 3 < r 4)
    (i j : Fin 6) (hi : i ≠ 5) (hj : j ≠ 5) :
    r i < r j ↔ branchRank (tag r) i < branchRank (tag r) j := by
  have h13 : r 1 ≠ r 3 := fun h => (by decide : (1 : Fin 6) ≠ 3) (hinj h)
  have h23 : r 2 ≠ r 3 := fun h => (by decide : (2 : Fin 6) ≠ 3) (hinj h)
  have h24 : r 2 ≠ r 4 := fun h => (by decide : (2 : Fin 6) ≠ 4) (hinj h)
  have h14 : r 1 ≠ r 4 := fun h => (by decide : (1 : Fin 6) ≠ 4) (hinj h)
  unfold tag
  split
  · split
    · fin_cases i <;> fin_cases j <;> simp [branchRank] at * <;> omega
    · split
      · fin_cases i <;> fin_cases j <;> simp [branchRank] at * <;> omega
      · fin_cases i <;> fin_cases j <;> simp [branchRank] at * <;> omega
  · split
    · fin_cases i <;> fin_cases j <;> simp [branchRank] at * <;> omega
    · split
      · fin_cases i <;> fin_cases j <;> simp [branchRank] at * <;> omega
      · fin_cases i <;> fin_cases j <;> simp [branchRank] at * <;> omega

private theorem table_rank_bound : ∀ p i : Fin 6, i ≠ 5 → branchRank p i < 5 := by decide

private theorem table_rank_inj :
    ∀ p i j : Fin 6, i ≠ 5 → j ≠ 5 → i ≠ j → branchRank p i ≠ branchRank p j := by decide

private theorem table_filter_card :
    ∀ p i : Fin 6, i ≠ 5 →
      (Finset.univ.filter fun j => j ≠ 5 ∧ branchRank p j < branchRank p i).card =
        branchRank p i := by decide

private theorem table_filter_card_le :
    ∀ p i : Fin 6, i ≠ 5 →
      (Finset.univ.filter fun j => j ≠ 5 ∧ branchRank p j ≤ branchRank p i).card =
        branchRank p i + 1 := by decide

private theorem tag_invariant (v : Fin 6 → α) (H : TwoArmShape v) (p : Fin 6) :
    BranchOrderInvariant (v 5) (v 0) (fun R : Ranking α n =>
      tag (fun i => (R.rank (v i)).val) = p) := by
  intro R T rel h
  have b (i : Fin 6) (hi : i ≠ 5) : Branch (v 5) (v 0) (v i) :=
    (H.branch _).mpr ⟨i, hi, rfl⟩
  have eq (i j : Fin 6) (hi : i ≠ 5) (hj : j ≠ 5) :
      (R.rank (v i)).val < (R.rank (v j)).val ↔ (T.rank (v i)).val < (T.rank (v j)).val :=
    rel _ _ (b i hi) (b j hj)
  unfold tag at h ⊢
  simp only [← eq 1 3 (by decide) (by decide), ← eq 2 3 (by decide) (by decide),
    ← eq 2 4 (by decide) (by decide), ← eq 4 1 (by decide) (by decide),
    ← eq 4 2 (by decide) (by decide)]
  exact h

private theorem beforeSet_card_le_five (v : Fin 6 → α) (H : TwoArmShape v) (R : Ranking α n) :
    (beforeSet R (v 5) (Branch (v 5) (v 0))).card < 6 := by
  classical
  let D : Finset (Fin 6) := Finset.univ.erase 5
  have hD : D.card = 5 := by decide
  have hs : beforeSet R (v 5) (Branch (v 5) (v 0)) ⊆ D.image v := by
    intro z hz
    obtain ⟨i, hi, rfl⟩ := (H.branch z).mp (mem_beforeSet.mp hz).1
    exact Finset.mem_image.mpr ⟨i, by simp [D,hi], rfl⟩
  have hc := (Finset.card_le_card hs).trans Finset.card_image_le
  omega

private theorem twoArm_rank_representation (v : Fin 6 → α) (H : TwoArmShape v)
    (R : Ranking α n) (i j : Fin 6) :
    R.rank (v i) < R.rank (v j) ↔
      TwoArmsMix.rank (tag (fun z => (R.rank (v z)).val)) ⟨_, beforeSet_card_le_five v H R⟩ i <
      TwoArmsMix.rank (tag (fun z => (R.rank (v z)).val)) ⟨_, beforeSet_card_le_five v H R⟩ j := by
  classical
  let r := fun z => (R.rank (v z)).val
  let p := tag r
  let B := beforeSet R (v 5) (Branch (v 5) (v 0))
  let k := B.card
  have hinj : Function.Injective r := fun _ _ e => H.inj (R.inj (Fin.ext e))
  have hh (u w : Fin 6) (hu : u ≠ 5) (hw : w ≠ 5) :
      r u < r w ↔ branchRank p u < branchRank p w :=
    tag_classifies r hinj (R.mono H.lower_x) (R.mono H.lower_y) (R.mono H.rail1)
      (R.mono H.rail2) u w hu hw
  have cut (u : Fin 6) (hu : u ≠ 5) :
      r 5 < r u ↔ k ≤ branchRank p u := by
    constructor
    · intro h
      let I := Finset.univ.filter fun z : Fin 6 => z ≠ 5 ∧ branchRank p z < branchRank p u
      have hsub : B ⊆ I.image v := by
        intro z hz
        obtain ⟨hzB, hzLt⟩ := mem_beforeSet.mp hz
        obtain ⟨w, hw, rfl⟩ := (H.branch z).mp hzB
        have hzR : r w < r 5 := hzLt
        have hm := (hh w u hw hu).mp (hzR.trans h)
        exact Finset.mem_image.mpr ⟨w, by simp [I, hw, hm], rfl⟩
      exact (Finset.card_le_card hsub).trans
        (Finset.card_image_le.trans_eq (table_filter_card p u hu))
    · intro h
      by_contra! hn
      have hult : r u < r 5 := lt_of_le_of_ne hn (fun e => hu (hinj e))
      let I := Finset.univ.filter fun z : Fin 6 => z ≠ 5 ∧ branchRank p z ≤ branchRank p u
      have hsub : I.image v ⊆ B := by
        intro z hz
        obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
        have hm : w ≠ 5 ∧ branchRank p w ≤ branchRank p u := by simpa [I] using hw
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
  change r i < r j ↔ TwoArmsMix.rank p ⟨k, _⟩ i < TwoArmsMix.rank p ⟨k, _⟩ j
  by_cases hi : i = 5
  · subst i
    by_cases hj : j = 5
    · subst j; simp
    · have hc := cut j hj
      simp only [TwoArmsMix.rank, ite_true, ite_eq_right hj]
      by_cases h : k ≤ branchRank p j <;> simp only [h, ite_true, ite_false] <;> omega
  · by_cases hj : j = 5
    · subst j
      have hc := cut i hi
      have hne : r i ≠ r 5 := fun e => hi (hinj e)
      simp only [TwoArmsMix.rank, ite_true, ite_eq_right hi]
      by_cases h : k ≤ branchRank p i <;> simp only [h, ite_true, ite_false] <;> omega
    · have hc := hh i j hi hj
      simp only [TwoArmsMix.rank, ite_eq_right hi, ite_eq_right hj]
      split <;> split <;> omega

/-- The five-vertex exclusive upset consisting of a root and two two-element
arms has a balanced pair if the root comparison has probability at most 1/4. -/
theorem balanced_of_twoArmShape (v : Fin 6 → α) (H : TwoArmShape v)
    (hba : ¬ v 0 ≤ v 5) (hd : ∀ z, z < v 5 → z < v 0)
    (hcap : 4 * pairCount (v 5) (v 0) n ≤ Nat.card (Ranking α n)) :
    ∃ x y : α, Balanced x y n :=
  balanced_of_twoArmClassification v H.inj hba hd (fun R => tag (fun z => (R.rank (v z)).val))
    (tag_invariant v H) (beforeSet_card_le_five v H) (twoArm_rank_representation v H) hcap

#print axioms balanced_of_twoArmShape
#print axioms balanced_of_twoArmClassification
end Balancing
end WidthThree

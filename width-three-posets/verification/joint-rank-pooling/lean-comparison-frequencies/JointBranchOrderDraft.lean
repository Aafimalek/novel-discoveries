/- Portable uncompiled draft connecting the checked arithmetic to actual rankings. -/
import MultiRankStep
import ConditionalBinListDraft
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Rat.Cast.Order

open scoped BigOperators

namespace WidthThree

noncomputable section

private abbrev countJoint {γ : Type*} (E : γ → Prop) := Nat.card {r : γ // E r}

private theorem countJoint_iff {γ : Type*} {E F : γ → Prop}
    (h : ∀ r, E r ↔ F r) : countJoint E = countJoint F :=
  Nat.card_congr (Equiv.subtypeEquivProp (funext fun r => propext (h r)))

private theorem countJoint_mono {γ : Type*} [Finite γ] {E F : γ → Prop}
    (h : ∀ r, E r → F r) : countJoint E ≤ countJoint F :=
  Nat.card_le_card_of_injective
    (fun r : {r : γ // E r} => (⟨r.val, h r.val r.property⟩ : {r : γ // F r}))
    (fun _ _ hr => Subtype.ext (congrArg (fun r : {r : γ // F r} => r.val) hr))

private theorem countJoint_split {γ : Type*} [Finite γ] (E F : γ → Prop) :
    countJoint E = countJoint (fun r => E r ∧ F r) + countJoint (fun r => E r ∧ ¬F r) := by
  classical
  let p : {r : γ // E r} → Prop := fun r => F r.val
  let e₁ : {r : {r : γ // E r} // p r} ≃ {r : γ // E r ∧ F r} :=
    { toFun := fun r => ⟨r.val.val, r.val.property, r.property⟩
      invFun := fun r => ⟨⟨r.val, r.property.1⟩, r.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let e₂ : {r : {r : γ // E r} // ¬ p r} ≃ {r : γ // E r ∧ ¬ F r} :=
    { toFun := fun r => ⟨r.val.val, r.val.property, r.property⟩
      invFun := fun r => ⟨⟨r.val, r.property.1⟩, r.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h := Nat.card_congr (Equiv.sumCompl p)
  rw [Nat.card_sum, Nat.card_congr e₁, Nat.card_congr e₂] at h
  exact h.symm

private theorem jointPartition {γ κ : Type*} [Finite γ] [Fintype κ]
    (E : γ → Prop) (tag : γ → κ) :
    countJoint E = ∑ t : κ, countJoint (fun r => E r ∧ tag r = t) := by
  let S := Σ t : κ, {r : γ // E r ∧ tag r = t}
  let e : {r : γ // E r} ≃ S :=
    { toFun := fun r => ⟨tag r.val, r.val, r.property, rfl⟩
      invFun := fun s => ⟨s.2.val, s.2.property.1⟩
      left_inv := fun _ => rfl
      right_inv := by
        rintro ⟨t,r,he,ht⟩
        subst t
        rfl }
  unfold countJoint
  rw [Nat.card_congr e]
  simp only [S, Nat.card_sigma]

variable {α : Type*} [PartialOrder α] [Fintype α] {n : ℕ}

private abbrev jointCutIndex (a b : α) (R : Ranking α n) :=
  (beforeSet R a (Branch a b)).card

private abbrev jointCondPrefix (a b : α) (E : Ranking α n → Prop) (k : ℕ) :=
  countJoint (fun R => E R ∧ jointCutIndex a b R < k)

private theorem jointCondPrefix_succ (a b : α) (E : Ranking α n → Prop) (k : ℕ) :
    jointCondPrefix a b E (k + 1) = jointCondPrefix a b E k + Nat.card (BinGiven a b k E) := by
  have h := countJoint_split (fun R => E R ∧ jointCutIndex a b R < k + 1)
    (fun R => jointCutIndex a b R < k)
  have h₁ : countJoint (fun R => (E R ∧ jointCutIndex a b R < k + 1) ∧ jointCutIndex a b R < k) =
      jointCondPrefix a b E k := by
    apply countJoint_iff
    intro R
    constructor
    · exact fun hr => ⟨hr.1.1,hr.2⟩
    · exact fun hr => ⟨⟨hr.1,Nat.lt_succ_of_lt hr.2⟩,hr.2⟩
  have h₂ : countJoint (fun R => (E R ∧ jointCutIndex a b R < k + 1) ∧ ¬ jointCutIndex a b R < k) =
      Nat.card (BinGiven a b k E) := by
    apply countJoint_iff
    intro R
    change ((E R ∧ jointCutIndex a b R < k + 1) ∧ ¬ jointCutIndex a b R < k) ↔
      jointCutIndex a b R = k ∧ E R
    constructor
    · exact fun hr => ⟨by have := hr.1.2; have := hr.2; omega,hr.1.1⟩
    · exact fun hr => ⟨⟨hr.2,by have := hr.1; omega⟩,by have := hr.1; omega⟩
  simpa only [h₁,h₂] using h

private theorem jointCondPrefix_zero (a b : α) (E : Ranking α n → Prop) :
    jointCondPrefix a b E 0 = 0 := by
  exact Nat.card_eq_zero.mpr (Or.inl ⟨fun R => Nat.not_lt_zero _ R.property.2⟩)

private theorem jointBefore_eq_condPrefix_of_constant
    {a b z : α} (hba : ¬ b ≤ a) (hz : Branch a b z) (E : Ranking α n → Prop)
    (k : ℕ) (hk : ∀ R, E R → branchPosition R a b z = k) :
    countJoint (fun R => E R ∧ R.rank a < R.rank z) = jointCondPrefix a b E k := by
  apply countJoint_iff
  intro R
  constructor
  · intro h
    have ht := (before_iff_cut_lt_branchPosition hba hz R).mp h.2
    change jointCutIndex a b R < branchPosition R a b z at ht
    rw [hk R h.1] at ht
    exact ⟨h.1, ht⟩
  · intro h
    refine ⟨h.1, (before_iff_cut_lt_branchPosition hba hz R).mpr ?_⟩
    change jointCutIndex a b R < branchPosition R a b z
    rw [hk R h.1]
    exact h.2

/-- Joint counting bound on an invariant fiber with fixed positions. -/
private theorem jointBefore_on_constant_positions
    {a b x y u v : α} (hba : ¬ b ≤ a) (hd : ∀ z, z < a → z < b)
    (hx : Branch a b x) (hy : Branch a b y) (hu : Branch a b u) (hv : Branch a b v)
    (E : Ranking α n → Prop) (hi : BranchOrderInvariant a b E)
    {r s d e m : ℕ} (hr : r ≤ m) (hs : s ≤ m) (h₁ : d ≤ m) (h₂ : e ≤ m)
    (hrx : ∀ R, E R → branchPosition R a b x = r)
    (hsy : ∀ R, E R → branchPosition R a b y = s)
    (hdu : ∀ R, E R → branchPosition R a b u = d)
    (hev : ∀ R, E R → branchPosition R a b v = e)
    (hjoint : r + s ≤ 2 * (d + e)) :
    countJoint (fun R => E R ∧ R.rank a < R.rank x) +
      countJoint (fun R => E R ∧ R.rank a < R.rank y) ≤
    2 * (countJoint (fun R => E R ∧ R.rank a < R.rank u) +
      countJoint (fun R => E R ∧ R.rank a < R.rank v)) := by
  rw [jointBefore_eq_condPrefix_of_constant hba hx E r hrx,
    jointBefore_eq_condPrefix_of_constant hba hy E s hsy,
    jointBefore_eq_condPrefix_of_constant hba hu E d hdu,
    jointBefore_eq_condPrefix_of_constant hba hv E e hev]
  exact JointPool.joint_of_prefix_step (fun k => Nat.card (BinGiven a b k E))
    (jointCondPrefix a b E) (jointCondPrefix_zero a b E)
    (jointCondPrefix_succ a b E)
    (fun k => natCard_binGiven_succ_le a b hba hd k E hi)
    hr hs h₁ h₂ hjoint

/-- Uniform-count numerator for 'a appears before z'. -/
abbrev jointComparisonCount (a z : α) : ℕ :=
  Nat.card {R : Ranking α n // R.rank a < R.rank z}

/-- Joint rank pooling for actual finite-poset rankings. -/
theorem jointComparisonCount_of_branchRankSum
    {a b x y u v : α} (hba : ¬ b ≤ a) (hd : ∀ z, z < a → z < b)
    (hx : Branch a b x) (hy : Branch a b y) (hu : Branch a b u) (hv : Branch a b v)
    (hjoint : ∀ R : Ranking α n, branchPosition R a b x + branchPosition R a b y ≤
      2 * (branchPosition R a b u + branchPosition R a b v)) :
    jointComparisonCount (n := n) a x + jointComparisonCount (n := n) a y ≤
      2 * (jointComparisonCount (n := n) a u + jointComparisonCount (n := n) a v) := by
  classical
  let m := Fintype.card α + 2
  have hbnd (R : Ranking α n) (z : α) : branchPosition R a b z < m := by
    have h := Finset.card_le_univ (beforeSet R z (Branch a b))
    unfold branchPosition m
    omega
  let Tag := Fin m × Fin m × Fin m × Fin m
  let f (R : Ranking α n) : Tag :=
    ⟨⟨_,hbnd R x⟩,⟨_,hbnd R y⟩,⟨_,hbnd R u⟩,⟨_,hbnd R v⟩⟩
  have hE (t : Tag) : BranchOrderInvariant a b (fun R => f R = t) := by
    intro R T h hRt
    have hf : f R = f T := by
      apply Prod.ext
      · exact Fin.ext (branchPosition_invariant hx h)
      · apply Prod.ext
        · exact Fin.ext (branchPosition_invariant hy h)
        · apply Prod.ext
          · exact Fin.ext (branchPosition_invariant hu h)
          · exact Fin.ext (branchPosition_invariant hv h)
    exact hf.symm.trans hRt
  let N (z : α) (t : Tag) : ℕ :=
    countJoint (fun R : Ranking α n => f R = t ∧ R.rank a < R.rank z)
  have hp (z : α) : jointComparisonCount (n := n) a z = ∑ t : Tag, N z t := by
    change countJoint (fun R : Ranking α n => R.rank a < R.rank z) = _
    rw [jointPartition _ f]
    apply Finset.sum_congr rfl
    intro t _
    exact countJoint_iff fun R => and_comm
  have hN (t : Tag) : N x t + N y t ≤ 2 * (N u t + N v t) := by
    by_cases hne : ∃ R, f R = t
    · obtain ⟨R, hR⟩ := hne
      subst t
      exact jointBefore_on_constant_positions hba hd hx hy hu hv
        (fun T => f T = f R) (hE (f R))
        ((hbnd R x).le) ((hbnd R y).le) ((hbnd R u).le) ((hbnd R v).le)
        (fun T hT => congrArg (fun z => z.1.val) hT)
        (fun T hT => congrArg (fun z => z.2.1.val) hT)
        (fun T hT => congrArg (fun z => z.2.2.1.val) hT)
        (fun T hT => congrArg (fun z => z.2.2.2.val) hT)
        (hjoint R)
    · have hzero (z : α) : N z t = 0 := by
        exact Nat.card_eq_zero.mpr (Or.inl ⟨fun R => hne ⟨R.val,R.property.1⟩⟩)
      simp only [hzero, Nat.add_zero, Nat.mul_zero, Nat.le_refl]
  calc
    jointComparisonCount (n := n) a x + jointComparisonCount (n := n) a y =
        ∑ t : Tag, (N x t + N y t) := by rw [Finset.sum_add_distrib, hp x, hp y]
    _ ≤ ∑ t : Tag, 2 * (N u t + N v t) := Finset.sum_le_sum (fun t _ => hN t)
    _ = 2 * (jointComparisonCount (n := n) a u + jointComparisonCount (n := n) a v) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, hp u, hp v]

/-- Rational uniform comparison frequency. On an empty population Lean
uses the usual zero-division convention; for a nonempty population this
is precisely the earlier-order probability. -/
def jointComparisonFrequency (a z : α) : ℚ :=
  (jointComparisonCount (n := n) a z : ℚ) / (Nat.card (Ranking α n) : ℚ)

/-- If F(z) is the comparison frequency of a before z, then the
pointwise joint rank hypothesis implies F(x)+F(y) ≤ 2(F(u)+F(v)). -/
theorem jointComparisonFrequency_of_branchRankSum
    {a b x y u v : α} (hba : ¬ b ≤ a) (hd : ∀ z, z < a → z < b)
    (hx : Branch a b x) (hy : Branch a b y) (hu : Branch a b u) (hv : Branch a b v)
    (hjoint : ∀ R : Ranking α n, branchPosition R a b x + branchPosition R a b y ≤
      2 * (branchPosition R a b u + branchPosition R a b v)) :
    jointComparisonFrequency (n := n) a x + jointComparisonFrequency (n := n) a y ≤
      2 * (jointComparisonFrequency (n := n) a u + jointComparisonFrequency (n := n) a v) := by
  have hN := jointComparisonCount_of_branchRankSum hba hd hx hy hu hv hjoint
  let K : ℚ := (Nat.card (Ranking α n) : ℚ)
  have hK : 0 ≤ K := by
    change (0 : ℚ) ≤ (Nat.card (Ranking α n) : ℚ)
    exact_mod_cast (Nat.zero_le (Nat.card (Ranking α n)))
  let c (z : α) : ℚ := (jointComparisonCount (n := n) a z : ℚ)
  have hc : c x + c y ≤ 2 * (c u + c v) := by
    dsimp only [c]
    exact_mod_cast hN
  change c x / K + c y / K ≤ 2 * (c u / K + c v / K)
  calc
    c x / K + c y / K = (c x + c y) / K := (add_div ..).symm
    _ ≤ (2 * (c u + c v)) / K := div_le_div_of_nonneg_right hc hK
    _ = 2 * (c u / K + c v / K) := by rw [mul_div_assoc, add_div]

#print axioms jointComparisonCount_of_branchRankSum
#print axioms jointComparisonFrequency_of_branchRankSum

end

end WidthThree

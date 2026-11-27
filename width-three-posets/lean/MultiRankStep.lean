import BranchOrder
import Mathlib.Basic.Finite.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace WidthThree

noncomputable section

private abbrev countLocal {γ : Type*} (E : γ → Prop) := Nat.card {r : γ // E r}

private theorem countLocal_iff {γ : Type*} {E F : γ → Prop}
    (h : ∀ r, E r ↔ F r) : countLocal E = countLocal F :=
  Nat.card_congr (Equiv.subtypeEquivProp (funext fun r => propext (h r)))

private theorem countLocal_mono {γ : Type*} [Finite γ] {E F : γ → Prop}
    (h : ∀ r, E r → F r) : countLocal E ≤ countLocal F :=
  Nat.card_le_card_of_injective
    (fun r : {r : γ // E r} => (⟨r.val, h r.val r.property⟩ : {r : γ // F r}))
    (fun _ _ hr => Subtype.ext (congrArg (fun r : {r : γ // F r} => r.val) hr))

private theorem countLocal_split {γ : Type*} [Finite γ] (E F : γ → Prop) :
    countLocal E = countLocal (fun r => E r ∧ F r) + countLocal (fun r => E r ∧ ¬F r) := by
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

private theorem countPartition {γ κ : Type*} [Finite γ] [Fintype κ]
    (E : γ → Prop) (tag : γ → κ) :
    countLocal E = ∑ t : κ, countLocal (fun r => E r ∧ tag r = t) := by
  let S := Σ t : κ, {r : γ // E r ∧ tag r = t}
  let e : {r : γ // E r} ≃ S :=
    { toFun := fun r => ⟨tag r.val, r.val, r.property, rfl⟩
      invFun := fun s => ⟨s.2.val, s.2.property.1⟩
      left_inv := fun _ => rfl
      right_inv := by
        rintro ⟨t,r,he,ht⟩
        subst t
        rfl }
  unfold countLocal
  rw [Nat.card_congr e]
  simp only [S, Nat.card_sigma]

variable {α : Type*} [PartialOrder α] [Fintype α] {n : ℕ}

/-- The one-based position of x in the order induced on the exclusive upset. -/
def branchPosition (R : Ranking α n) (a b x : α) : ℕ :=
  (beforeSet R x (Branch a b)).card + 1

private abbrev cutIndex (a b : α) (R : Ranking α n) :=
  (beforeSet R a (Branch a b)).card

theorem branchPosition_invariant {a b x : α} (hx : Branch a b x)
    {R T : Ranking α n} (h : ∀ u v, Branch a b u → Branch a b v →
      (R.rank u < R.rank v ↔ T.rank u < T.rank v)) :
    branchPosition R a b x = branchPosition T a b x := by
  have he : beforeSet R x (Branch a b) = beforeSet T x (Branch a b) := by
    ext u
    rw [mem_beforeSet, mem_beforeSet]
    constructor
    · exact fun p => ⟨p.1, (h u x p.1 hx).mp p.2⟩
    · exact fun p => ⟨p.1, (h u x p.1 hx).mpr p.2⟩
  simp only [branchPosition, he]

theorem before_iff_cut_lt_branchPosition {a b x : α} (hba : ¬b ≤ a) (hx : Branch a b x)
    (R : Ranking α n) :
    R.rank a < R.rank x ↔ cutIndex a b R < branchPosition R a b x := by
  classical
  constructor
  · intro h
    have hs : beforeSet R a (Branch a b) ⊆ beforeSet R x (Branch a b) :=
      fun _ hz => let p := mem_beforeSet.mp hz
        mem_beforeSet.mpr ⟨p.1, p.2.trans h⟩
    have hc := Finset.card_le_card hs
    unfold branchPosition cutIndex
    omega
  · intro h
    by_contra! hnot
    have hax : R.rank a ≠ R.rank x := fun e => hba (R.inj e ▸ hx.1)
    have hxa : R.rank x < R.rank a := lt_of_le_of_ne hnot hax.symm
    have hs : insert x (beforeSet R x (Branch a b)) ⊆ beforeSet R a (Branch a b) := by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact mem_beforeSet.mpr ⟨hx,hxa⟩
      · obtain ⟨hzB,hzx⟩ := mem_beforeSet.mp hz
        exact mem_beforeSet.mpr ⟨hzB,hzx.trans hxa⟩
    have hc := Finset.card_le_card hs
    have hn : x ∉ beforeSet R x (Branch a b) := fun hx => lt_irrefl _ (mem_beforeSet.mp hx).2
    rw [Finset.card_insert_of_notMem hn] at hc
    exact (not_lt_of_ge hc) h

private abbrev condPrefix (a b : α) (E : Ranking α n → Prop) (k : ℕ) :=
  countLocal (fun R => E R ∧ cutIndex a b R < k)

private theorem condPrefix_succ (a b : α) (E : Ranking α n → Prop) (k : ℕ) :
    condPrefix a b E (k + 1) = condPrefix a b E k + Nat.card (BinGiven a b k E) := by
  have h := countLocal_split (fun R => E R ∧ cutIndex a b R < k + 1)
    (fun R => cutIndex a b R < k)
  have h₁ : countLocal (fun R => (E R ∧ cutIndex a b R < k + 1) ∧ cutIndex a b R < k) =
      condPrefix a b E k := by
    apply countLocal_iff
    intro R
    constructor
    · exact fun hr => ⟨hr.1.1,hr.2⟩
    · exact fun hr => ⟨⟨hr.1,Nat.lt_succ_of_lt hr.2⟩,hr.2⟩
  have h₂ : countLocal (fun R => (E R ∧ cutIndex a b R < k + 1) ∧ ¬ cutIndex a b R < k) =
      Nat.card (BinGiven a b k E) := by
    apply countLocal_iff
    intro R
    change ((E R ∧ cutIndex a b R < k + 1) ∧ ¬ cutIndex a b R < k) ↔
      cutIndex a b R = k ∧ E R
    constructor
    · exact fun hr => ⟨by have := hr.1.2; have := hr.2; omega,hr.1.1⟩
    · exact fun hr => ⟨⟨hr.2,by have := hr.1; omega⟩,by have := hr.1; omega⟩
  simpa only [h₁,h₂] using h

private theorem condPrefix_subadd (a b : α) (hba : ¬ b ≤ a) (hd : ∀ z, z < a → z < b)
    (E : Ranking α n → Prop) (hi : BranchOrderInvariant a b E) (j k : ℕ) :
    condPrefix a b E (j + k) ≤ condPrefix a b E j + condPrefix a b E k := by
  have hq : Antitone (fun i : ℕ => Nat.card (BinGiven a b i E)) :=
    antitone_nat_of_succ_le (fun i => natCard_binGiven_succ_le a b hba hd i E hi)
  induction k with
  | zero => simp only [Nat.add_zero]; exact Nat.le_add_right _ _
  | succ k ih =>
    have hk := hq (Nat.le_add_left k j)
    change Nat.card (BinGiven a b (j+k) E) ≤ Nat.card (BinGiven a b k E) at hk
    rw [Nat.add_succ, condPrefix_succ, condPrefix_succ]
    omega

/-- The pooled rank inequality inside any order-invariant fibre. -/
theorem countLocal_before_le_add_of_conditionalPositions
    {a b u w v : α} (hba : ¬ b ≤ a) (hd : ∀ z, z < a → z < b)
    (hu : Branch a b u) (hw : Branch a b w) (hv : Branch a b v)
    (E : Ranking α n → Prop) (hi : BranchOrderInvariant a b E)
    (j k : ℕ)
    (h₁ : ∀ R, E R → j ≤ branchPosition R a b u)
    (h₂ : ∀ R, E R → k ≤ branchPosition R a b w)
    (h₃ : ∀ R, E R → branchPosition R a b v ≤ j + k) :
    countLocal (fun R => E R ∧ R.rank a < R.rank v) ≤
      countLocal (fun R => E R ∧ R.rank a < R.rank u) +
      countLocal (fun R => E R ∧ R.rank a < R.rank w) := by
  have hl : countLocal (fun R => E R ∧ R.rank a < R.rank v) ≤ condPrefix a b E (j+k) :=
    countLocal_mono (fun R hr =>
      ⟨hr.1, lt_of_lt_of_le ((before_iff_cut_lt_branchPosition hba hv R).mp hr.2) (h₃ R hr.1)⟩)
  have hu' : condPrefix a b E j ≤ countLocal (fun R => E R ∧ R.rank a < R.rank u) :=
    countLocal_mono (fun R hr =>
      ⟨hr.1, (before_iff_cut_lt_branchPosition hba hu R).mpr (lt_of_lt_of_le hr.2 (h₁ R hr.1))⟩)
  have hw' : condPrefix a b E k ≤ countLocal (fun R => E R ∧ R.rank a < R.rank w) :=
    countLocal_mono (fun R hr =>
      ⟨hr.1, (before_iff_cut_lt_branchPosition hba hw R).mpr (lt_of_lt_of_le hr.2 (h₂ R hr.1))⟩)
  exact hl.trans ((condPrefix_subadd a b hba hd E hi j k).trans (Nat.add_le_add hu' hw'))

/-- If in every induced branch order the position of v is no more than the
sum of the positions of u and w, the comparison count for v is bounded by
the sum of their comparison counts. Two different anchors may be pooled. -/
theorem pairCount_le_add_of_pooledBranchPositions
    {a b u w v : α} (hba : ¬ b ≤ a) (hd : ∀ z, z < a → z < b)
    (hu : Branch a b u) (hw : Branch a b w) (hv : Branch a b v)
    (hc : ∀ R : Ranking α n, branchPosition R a b v ≤ branchPosition R a b u + branchPosition R a b w) :
    (Nat.card {R : Ranking α n // R.rank a < R.rank v}) ≤
      (Nat.card {R : Ranking α n // R.rank a < R.rank u}) +
      (Nat.card {R : Ranking α n // R.rank a < R.rank w}) := by
  classical
  let m := Fintype.card α + 2
  have hbnd (R : Ranking α n) (x : α) : branchPosition R a b x < m := by
    have h := Finset.card_le_univ (beforeSet R x (Branch a b))
    unfold branchPosition m
    omega
  let f (R : Ranking α n) : Fin m × Fin m × Fin m :=
    ⟨⟨_,hbnd R u⟩,⟨_,hbnd R w⟩,⟨_,hbnd R v⟩⟩
  have hE (t : Fin m × Fin m × Fin m) : BranchOrderInvariant a b (fun R => f R = t) := by
    intro R T hb hRt
    have hf : f R = f T := by
      apply Prod.ext
      · exact Fin.ext (branchPosition_invariant hu hb)
      · apply Prod.ext
        · exact Fin.ext (branchPosition_invariant hw hb)
        · exact Fin.ext (branchPosition_invariant hv hb)
    exact hf.symm.trans hRt
  change countLocal (fun R : Ranking α n => R.rank a < R.rank v) ≤
    countLocal (fun R : Ranking α n => R.rank a < R.rank u) +
    countLocal (fun R : Ranking α n => R.rank a < R.rank w)
  rw [countPartition _ f, countPartition _ f, countPartition _ f, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro t ht
  have comm (R : Ranking α n) (x : α) :
      (R.rank a < R.rank x ∧ f R = t) ↔ (f R = t ∧ R.rank a < R.rank x) := and_comm
  simp only [comm]
  by_cases he : ∃ R, f R = t
  · obtain ⟨R, hR⟩ := he
    subst t
    refine countLocal_before_le_add_of_conditionalPositions hba hd hu hw hv (fun T => f T = f R)
      (hE (f R)) (branchPosition R a b u) (branchPosition R a b w) ?_ ?_ ?_
    · intro T h
      exact (congrArg (fun p => p.1.val) h).ge
    · intro T h
      exact (congrArg (fun p => p.2.1.val) h).ge
    · intro T h
      exact (congrArg (fun p => p.2.2.val) h).le.trans (hc R)
  · have hzero : countLocal (fun R : Ranking α n => f R = t ∧ R.rank a < R.rank v) = 0 := by
      exact Nat.card_eq_zero.mpr (Or.inl ⟨fun R => he ⟨R.val,R.property.1⟩⟩)
    omega

private theorem branchPosition_lt_of_before {a b u w : α} (R : Ranking α n)
    (hu : Branch a b u) (huw : R.rank u < R.rank w) :
    branchPosition R a b u < branchPosition R a b w := by
  classical
  let U := beforeSet R u (Branch a b)
  let W := beforeSet R w (Branch a b)
  have hSub : U ⊆ W := fun _ hz =>
    let he := mem_beforeSet.mp hz
    mem_beforeSet.mpr ⟨he.1, he.2.trans huw⟩
  have hNot : u ∉ U := fun hz => lt_irrefl _ (mem_beforeSet.mp hz).2
  have hMem : u ∈ W := mem_beforeSet.mpr ⟨hu,huw⟩
  have hStrict : U ⊂ W := Finset.ssubset_iff_subset_ne.mpr ⟨hSub, fun eq => hNot (eq ▸ hMem)⟩
  have hh := Finset.card_lt_card hStrict
  exact Nat.add_lt_add_right hh 1

/-- At least one strict predecessor in the branch forces position at least two. -/
theorem two_le_branchPosition_of_branch_below {a b z x : α} (R : Ranking α n)
    (hz : Branch a b z) (h : z < x) : 2 ≤ branchPosition R a b x := by
  have hm : z ∈ beforeSet R x (Branch a b) := mem_beforeSet.mpr ⟨hz, R.mono h⟩
  have hp := Finset.card_pos.mpr ⟨z,hm⟩
  unfold branchPosition
  omega

/-- For any branch with at most five points, two distinct strict successors of
its root form a pool that controls every branch vertex. No comparability
between the other vertices is required. -/
theorem pairCount_le_add_of_branch_card_le_five
    {a b u w v : α} (hba : ¬ b ≤ a) (hd : ∀ z, z < a → z < b)
    (hb : Branch a b b) (hu : Branch a b u) (hw : Branch a b w) (hv : Branch a b v)
    (hbu : b < u) (hbw : b < w) (huw : u ≠ w)
    (hsize : Nat.card {z : α // Branch a b z} ≤ 5) :
    (Nat.card {R : Ranking α n // R.rank a < R.rank v}) ≤
      (Nat.card {R : Ranking α n // R.rank a < R.rank u}) +
      (Nat.card {R : Ranking α n // R.rank a < R.rank w}) := by
  classical
  apply pairCount_le_add_of_pooledBranchPositions hba hd hu hw hv
  intro R
  have hu2 := two_le_branchPosition_of_branch_below R hb hbu
  have hw2 := two_le_branchPosition_of_branch_below R hb hbw
  have hn : R.rank u ≠ R.rank w := fun h => huw (R.inj h)
  have hp : branchPosition R a b u + branchPosition R a b w ≥ 5 := by
    rcases lt_or_gt_of_ne hn with h | h
    · have hh := branchPosition_lt_of_before R hu h
      omega
    · have hh := branchPosition_lt_of_before R hw h
      omega
  let B := Finset.univ.filter (Branch a b)
  have hB : B.card = Nat.card {z : α // Branch a b z} := by
    rw [← Fintype.card_coe, ← Nat.card_eq_fintype_card]
    apply Nat.card_congr
    apply Equiv.subtypeEquivProp
    funext z
    apply propext
    simp [B]
  have hm : v ∉ beforeSet R v (Branch a b) := fun h => lt_irrefl _ (mem_beforeSet.mp h).2
  have hSub : insert v (beforeSet R v (Branch a b)) ⊆ B := by
    intro z hz
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hv
    · exact (mem_beforeSet.mp hz).1
  have hh := Finset.card_le_card hSub
  rw [Finset.card_insert_of_notMem hm, hB] at hh
  exact hh.trans (hsize.trans hp)

/-- The branch downset of x, including x when x is in the branch. -/
def pooledLower (a b x : α) : Finset α := by
  classical
  exact Finset.univ.filter (fun z => Branch a b z ∧ z ≤ x)

/-- The branch vertices that are not strict successors of x. -/
def pooledUpper (a b x : α) : Finset α := by
  classical
  exact Finset.univ.filter (fun z => Branch a b z ∧ ¬ x < z)

private theorem mem_pooledLower {a b x z : α} :
    z ∈ pooledLower a b x ↔ Branch a b z ∧ z ≤ x := by
  classical
  simp [pooledLower]

private theorem mem_pooledUpper {a b x z : α} :
    z ∈ pooledUpper a b x ↔ Branch a b z ∧ ¬ x < z := by
  classical
  simp [pooledUpper]

/-- A static pooled-rank bound. The early anchor accounts for the smaller
downset, and the late anchor accounts for the entire union of downsets. -/
theorem pairCount_le_add_of_branchDownsetUnion
    {a b u w v : α} (hba : ¬ b ≤ a) (hd : ∀ z, z < a → z < b)
    (hu : Branch a b u) (hw : Branch a b w) (hv : Branch a b v)
    (hh : ∀ _ : DecidableEq α,
      (pooledUpper a b v).card ≤ min (pooledLower a b u).card (pooledLower a b w).card +
        ((pooledLower a b u) ∪ (pooledLower a b w)).card) :
    (Nat.card {R : Ranking α n // R.rank a < R.rank v}) ≤
      (Nat.card {R : Ranking α n // R.rank a < R.rank u}) +
      (Nat.card {R : Ranking α n // R.rank a < R.rank w}) := by
  classical
  apply pairCount_le_add_of_pooledBranchPositions hba hd hu hw hv
  intro R
  let P (x : α) := insert x (beforeSet R x (Branch a b))
  have cardP (x : α) : (P x).card = branchPosition R a b x := by
    have hxx : x ∉ beforeSet R x (Branch a b) := fun h => lt_irrefl _ (mem_beforeSet.mp h).2
    exact Finset.card_insert_of_notMem hxx
  have memP (x z : α) (hx : Branch a b x) :
      z ∈ P x ↔ Branch a b z ∧ R.rank z ≤ R.rank x := by
    change z ∈ insert x (beforeSet R x (Branch a b)) ↔ _
    constructor
    · intro hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact ⟨hx,le_rfl⟩
      · exact ⟨(mem_beforeSet.mp hz).1, (mem_beforeSet.mp hz).2.le⟩
    · intro hz
      by_cases he : z = x
      · exact Finset.mem_insert.mpr (Or.inl he)
      · exact Finset.mem_insert.mpr (Or.inr (mem_beforeSet.mpr
          ⟨hz.1, lt_of_le_of_ne hz.2 (fun e => he (R.inj e))⟩))
  have hV : branchPosition R a b v ≤ (pooledUpper a b v).card := by
    rw [← cardP]
    apply Finset.card_le_card
    intro z hz
    obtain ⟨hbz,hzv⟩ := (memP v z hv).mp hz
    exact mem_pooledUpper.mpr ⟨hbz, fun h => (not_lt_of_ge hzv) (R.mono h)⟩
  have lowerToPrefix (x y : α) (hy : Branch a b y) (hxy : R.rank x ≤ R.rank y) :
      pooledLower a b x ⊆ P y := by
    intro z hz
    obtain ⟨hzB,hzx⟩ := mem_pooledLower.mp hz
    exact (memP y z hy).mpr ⟨hzB, (R.mono.monotone hzx).trans hxy⟩
  let lo := min (pooledLower a b u).card (pooledLower a b w).card
  let un := ((pooledLower a b u) ∪ (pooledLower a b w)).card
  have hstatic : (pooledUpper a b v).card ≤ lo + un := hh (Classical.decEq α)
  have hsum : lo + un ≤ branchPosition R a b u + branchPosition R a b w := by
    rcases le_total (R.rank u) (R.rank w) with h | h
    · have h₁ : lo ≤ branchPosition R a b u :=
        (min_le_left _ _).trans ((Finset.card_le_card (lowerToPrefix u u hu le_rfl)).trans_eq (cardP u))
      have h₂ : un ≤ branchPosition R a b w :=
        (Finset.card_le_card (Finset.union_subset
          (lowerToPrefix u w hw h) (lowerToPrefix w w hw le_rfl))).trans_eq (cardP w)
      exact Nat.add_le_add h₁ h₂
    · have h₁ : lo ≤ branchPosition R a b w :=
        (min_le_right _ _).trans ((Finset.card_le_card (lowerToPrefix w w hw le_rfl)).trans_eq (cardP w))
      have h₂ : un ≤ branchPosition R a b u :=
        (Finset.card_le_card (Finset.union_subset
          (lowerToPrefix u u hu le_rfl) (lowerToPrefix w u hu h))).trans_eq (cardP u)
      exact (Nat.add_le_add h₁ h₂).trans_eq (Nat.add_comm _ _)
  exact hV.trans (hstatic.trans hsum)

end

#print axioms pairCount_le_add_of_pooledBranchPositions
#print axioms pairCount_le_add_of_branch_card_le_five
#print axioms pairCount_le_add_of_branchDownsetUnion

end WidthThree

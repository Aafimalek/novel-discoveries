/- Full structural assembly draft: static only; not yet compiled. -/
import DiagonalAnchorsDraft
import Mathlib.Data.Nat.Find
import Mathlib.Basic.Finite.Sum

namespace WidthThree.Diagonal

noncomputable section

variable {α : Type*} [PartialOrder α] [Fintype α]
variable {a b : α} {n h r t : ℕ}

def ComparisonLow (a z : α) (n : ℕ) : Prop :=
  3 * jointComparisonCount (n := n) a z < Nat.card (Ranking α n)

def ComparisonHigh (a z : α) (n : ℕ) : Prop :=
  2 * Nat.card (Ranking α n) < 3 * jointComparisonCount (n := n) a z

/-- Integer form of the closed interval of balanced comparisons. -/
def ComparisonBalanced (a z : α) (n : ℕ) : Prop :=
  a ≠ z ∧ Nat.card (Ranking α n) ≤ 3 * jointComparisonCount (n := n) a z ∧
    3 * jointComparisonCount (n := n) a z ≤ 2 * Nat.card (Ranking α n)

omit [Fintype α] in
private theorem notBalanced_cases {z : α} (hne : a ≠ z)
    (hnot : ¬ ComparisonBalanced a z n) : ComparisonLow a z n ∨ ComparisonHigh a z n := by
  unfold ComparisonLow ComparisonHigh
  by_cases hl : 3 * jointComparisonCount (n := n) a z < Nat.card (Ranking α n)
  · exact Or.inl hl
  · right
    by_contra hh
    exact hnot ⟨hne, by omega, by omega⟩

omit [Fintype α] in
private theorem low_of_notBalanced_and_half {z : α} (hne : a ≠ z)
    (hnot : ¬ ComparisonBalanced a z n)
    (hh : 2*jointComparisonCount (n := n) a z ≤ Nat.card (Ranking α n)) :
    ComparisonLow a z n := by
  rcases notBalanced_cases hne hnot with hl | hu
  · exact hl
  · unfold ComparisonHigh at hu
    omega

omit [Fintype α] in
private theorem branch_ne (hba : ¬ b ≤ a) {z : α} (hz : Branch a b z) : a ≠ z :=
  fun e => hba (e ▸ hz.1)

/-- A pooled comparison measured against two low anchors is low under the
no-balance classification. -/
private theorem low_of_pooled {u v z : α} (hba : ¬ b ≤ a) (hd : ∀ w, w < a → w < b)
    (hu : Branch a b u) (hv : Branch a b v) (hz : Branch a b z)
    (huL : ComparisonLow a u n) (hvL : ComparisonLow a v n)
    (hclass : ComparisonLow a z n ∨ ComparisonHigh a z n)
    (hrank : ∀ R : Ranking α n, branchPosition R a b z ≤
      branchPosition R a b u + branchPosition R a b v) :
    ComparisonLow a z n := by
  rcases hclass with h | h
  · exact h
  · have hc : jointComparisonCount (n := n) a z ≤
        jointComparisonCount (n := n) a u + jointComparisonCount (n := n) a v :=
      pairCount_le_add_of_pooledBranchPositions hba hd hu hv hz hrank
    unfold ComparisonLow at huL hvL
    unfold ComparisonHigh at h
    omega

/-- The exact rank of a point in the common ordered prefix. -/
theorem Labels.prefix_branchPosition (L : Labels a b h r t) (R : Ranking α n)
    (hmono : StrictMono (fun k : Fin h => L.q k)) (i : Fin h) :
    branchPosition R a b (L.q i) = i.val+1 := by
  classical
  let f : Fin i.val → α := fun j => L.q (Fin.castLE (Nat.le_of_lt i.isLt) j)
  have hf : Function.Injective f := hmono.injective.comp
    (Fin.castLE_injective (Nat.le_of_lt i.isLt))
  have he : beforeSet R (L.q i) (Branch a b) = Finset.univ.image f := by
    ext z
    constructor
    · intro hz
      obtain ⟨hzB,hzR⟩ := mem_beforeSet.mp hz
      obtain ⟨w,rfl⟩ := (L.branch_iff _).mp hzB
      rcases w with w | w
      · have hwi : w.val < i.val := by
          by_contra hn
          have hle : i ≤ w := by
            change i.val ≤ w.val
            omega
          exact (not_lt_of_ge (R.mono.monotone (hmono.monotone hle))) hzR
        let j : Fin i.val := ⟨w.val,hwi⟩
        have hj : Fin.castLE (Nat.le_of_lt i.isLt) j = w := Fin.ext rfl
        exact Finset.mem_image.mpr ⟨j,Finset.mem_univ _,congrArg L.q hj⟩
      · rcases w with w | w
        · exact ((not_lt_of_ge (le_of_lt (R.mono (L.prefix_x i w)))) hzR).elim
        · exact ((not_lt_of_ge (le_of_lt (R.mono (L.prefix_y i w)))) hzR).elim
    · intro hz
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hz
      apply mem_beforeSet.mpr
      refine ⟨L.branch_label _, R.mono (hmono ?_)⟩
      change j.val < i.val
      exact j.isLt
  unfold branchPosition
  rw [he, Finset.card_image_of_injective _ hf]
  simp

private theorem all_prefix_low (L : Labels a b h r t)
    (hba : ¬ b ≤ a) (hd : ∀ w, w < a → w < b)
    (hmono : StrictMono (fun k : Fin h => L.q k))
    (hfirst : ∀ k : Fin h, k.val = 0 → L.q k = b)
    (hb : ComparisonLow a b n)
    (hclass : ∀ z, Branch a b z → ComparisonLow a z n ∨ ComparisonHigh a z n) :
    ∀ k : Fin h, ComparisonLow a (L.q k) n := by
  have H : ∀ m : ℕ, ∀ k : Fin h, k.val = m → ComparisonLow a (L.q k) n := by
    intro m
    induction m with
    | zero =>
        intro k hk
        rw [hfirst k hk]
        exact hb
    | succ m ih =>
        intro k hk
        have hmh : m < h := by have hkh := k.isLt; omega
        let u : Fin h := ⟨m,hmh⟩
        have hu := ih u rfl
        apply low_of_pooled hba hd (L.branch_label (Sum.inl u)) (L.branch_label (Sum.inl u))
          (L.branch_label (Sum.inl k)) hu hu (hclass _ (L.branch_label (Sum.inl k)))
        intro R
        rw [L.prefix_branchPosition R hmono k, L.prefix_branchPosition R hmono u]
        change k.val+1 ≤ (m+1)+(m+1)
        omega
  intro k
  exact H k.val k rfl

private theorem all_low_or_first_high {s : ℕ} (low high : Fin s → Prop)
    (hclass : ∀ k, low k ∨ high k) :
    (∀ k, low k) ∨ ∃ i, high i ∧ ∀ k, k.val < i.val → low k := by
  classical
  by_cases hex : ∃ i, high i
  · let P : ℕ → Prop := fun m => ∃ i : Fin s, i.val = m ∧ high i
    have hp : ∃ m, P m := by
      obtain ⟨i,hi⟩ := hex
      exact ⟨i.val,i,rfl,hi⟩
    obtain ⟨i,hei,hhi⟩ := Nat.find_spec hp
    refine Or.inr ⟨i,hhi,fun k hk => ?_⟩
    rcases hclass k with hl | hh
    · exact hl
    · have hm : Nat.find hp ≤ k.val := Nat.find_min' hp ⟨k,rfl,hh⟩
      omega
  · exact Or.inl (fun k => (hclass k).resolve_right (fun hh => hex ⟨k,hh⟩))

/-- The event that the entire exclusive branch occurs before a. -/
def finalCut (a b : α) (R : Ranking α n) : Prop :=
  ∀ z, Branch a b z → R.rank z < R.rank a

/-- From the checked single-step branch swap, the last cut is no larger
than the initial comparison event. -/
theorem finalCut_card_le_root_count
    (hba : ¬ b ≤ a) (hd : ∀ z, z < a → z < b) (hb : Branch a b b) :
    Nat.card {R : Ranking α n // finalCut a b R} ≤ jointComparisonCount (n := n) a b := by
  classical
  let B : Finset α := Finset.univ.filter (Branch a b)
  have he (R : {R : Ranking α n // finalCut a b R}) :
      beforeSet R.val a (Branch a b) = B := by
    ext z
    constructor
    · intro hz
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(mem_beforeSet.mp hz).1⟩
    · intro hz
      have hzB : Branch a b z := (Finset.mem_filter.mp hz).2
      exact mem_beforeSet.mpr ⟨hzB,R.property z hzB⟩
  let f : {R : Ranking α n // finalCut a b R} → Bin a b B.card n :=
    fun R => ⟨R.val,congrArg Finset.card (he R)⟩
  have hf : Function.Injective f := fun _ _ he =>
    Subtype.ext (congrArg (fun R : Bin a b B.card n => R.val) he)
  have hm : Nat.card (Bin a b B.card n) ≤ Nat.card (Bin a b 0 n) :=
    (antitone_nat_of_succ_le (f := fun k => Nat.card (Bin a b k n))
      (fun k => natCard_bin_succ_le (n := n) a b hba hd k)) (Nat.zero_le B.card)
  let g : Bin a b 0 n → {R : Ranking α n // R.rank a < R.rank b} := fun R =>
    ⟨R.val, by
      have hn : ¬ R.val.rank b < R.val.rank a := by
        intro hlt
        have hpos : 0 < (beforeSet R.val a (Branch a b)).card :=
          Finset.card_pos.mpr ⟨b,mem_beforeSet.mpr ⟨hb,hlt⟩⟩
        have hzero : (beforeSet R.val a (Branch a b)).card = 0 := R.property
        omega
      have hne : R.val.rank a ≠ R.val.rank b := fun h => branch_ne hba hb (R.val.inj h)
      exact lt_of_le_of_ne (le_of_not_gt hn) hne⟩
  have hg : Function.Injective g := fun _ _ he =>
    Subtype.ext (congrArg (fun R : {R : Ranking α n // R.rank a < R.rank b} => R.val) he)
  exact (Nat.card_le_card_of_injective f hf).trans
    (hm.trans (Nat.card_le_card_of_injective g hg))

private theorem count_cover_three {γ : Type*} [Finite γ]
    (A B C : γ → Prop) (hcover : ∀ x, A x ∨ B x ∨ C x) :
    Nat.card γ ≤ Nat.card {x // A x} + Nat.card {x // B x} + Nat.card {x // C x} := by
  classical
  let f : γ → {x // A x} ⊕ ({x // B x} ⊕ {x // C x}) := fun x =>
    if ha : A x then Sum.inl ⟨x,ha⟩ else
    if hb : B x then Sum.inr (Sum.inl ⟨x,hb⟩) else
      Sum.inr (Sum.inr ⟨x,((hcover x).resolve_left ha).resolve_left hb⟩)
  let inverse : {x // A x} ⊕ ({x // B x} ⊕ {x // C x}) → γ :=
    Sum.elim Subtype.val (Sum.elim Subtype.val Subtype.val)
  have hl : Function.LeftInverse inverse f := by
    intro x
    by_cases ha : A x
    · simp [f,inverse,ha]
    · by_cases hb : B x <;> simp [f,inverse,ha,hb]
  have h := Nat.card_le_card_of_injective f hl.injective
  simpa only [Nat.card_sum, Nat.add_assoc] using h

private theorem low_cover_false {u v : α} (hba : ¬ b ≤ a) (hd : ∀ w, w < a → w < b)
    (hb : Branch a b b) (hbLow : ComparisonLow a b n)
    (hu : ComparisonLow a u n) (hv : ComparisonLow a v n)
    (hdom : ∀ z, Branch a b z → z ≤ u ∨ z ≤ v) : False := by
  have hcov := count_cover_three
    (fun R : Ranking α n => R.rank a < R.rank u) (fun R => R.rank a < R.rank v)
    (finalCut a b) (fun R => by
      by_cases hU : R.rank a < R.rank u
      · exact Or.inl hU
      by_cases hV : R.rank a < R.rank v
      · exact Or.inr (Or.inl hV)
      right
      right
      intro z hz
      have hne : R.rank z ≠ R.rank a := fun e => (branch_ne hba hz) (R.inj e.symm)
      apply lt_of_le_of_ne _ hne
      rcases hdom z hz with h | h
      · exact (R.mono.monotone h).trans (le_of_not_gt hU)
      · exact (R.mono.monotone h).trans (le_of_not_gt hV))
  have hlast := finalCut_card_le_root_count (n := n) hba hd hb
  unfold ComparisonLow at hbLow hu hv
  change Nat.card (Ranking α n) ≤
    jointComparisonCount (n := n) a u + jointComparisonCount (n := n) a v +
      Nat.card {R : Ranking α n // finalCut a b R} at hcov
  omega

private theorem all_rails_low_false (L : Labels a b h r t)
    (hba : ¬ b ≤ a) (hd : ∀ w, w < a → w < b)
    (hb : Branch a b b) (hbLow : ComparisonLow a b n)
    (qIdx : Fin h) (hq : ∀ k : Fin h, L.q k ≤ L.q qIdx)
    (hqLow : ComparisonLow a (L.q qIdx) n)
    (hx : ∀ k : Fin r, ComparisonLow a (L.x k) n)
    (hy : ∀ k : Fin t, ComparisonLow a (L.y k) n) : False := by
  let u := L.lowAnchorX qIdx r le_rfl
  let v := L.lowAnchorY qIdx t le_rfl
  have hu : ComparisonLow a u n :=
    L.lowAnchorX_property qIdx le_rfl (fun z => ComparisonLow a z n) hqLow (fun k _ => hx k)
  have hv : ComparisonLow a v n :=
    L.lowAnchorY_property qIdx le_rfl (fun z => ComparisonLow a z n) hqLow (fun k _ => hy k)
  apply low_cover_false hba hd hb hbLow hu hv
  intro z hz
  obtain ⟨w,rfl⟩ := (L.branch_iff _).mp hz
  rcases w with w | w
  · left
    by_cases hr : r = 0
    · simpa only [u,Labels.lowAnchorX,dite_eq_left hr] using hq w
    · simpa only [u,Labels.lowAnchorX,dite_eq_right hr] using (L.prefix_x w ⟨r-1,by omega⟩).le
  · rcases w with w | w
    · left
      have hw := w.isLt
      have hr : r ≠ 0 := by omega
      change L.x w ≤ L.lowAnchorX qIdx r le_rfl
      rw [Labels.lowAnchorX,dite_eq_right hr]
      apply L.x_mono.monotone
      change w.val ≤ r-1
      omega
    · right
      have hw := w.isLt
      have ht : t ≠ 0 := by omega
      change L.y w ≤ L.lowAnchorY qIdx t le_rfl
      rw [Labels.lowAnchorY,dite_eq_right ht]
      apply L.y_mono.monotone
      change w.val ≤ t-1
      omega

/-- Reuse the finite-end gate upper bound with a deliberately vacuous
gate offset, then absorb its extra room with the genuine imbalance bonus. -/
private theorem one_high_X_false (L : Labels a b h r t)
    (hba : ¬ b ≤ a) (hd : ∀ w, w < a → w < b)
    (hh : 2 ≤ h)
    (qIdx : Fin h) (hq : ∀ k : Fin h, L.q k ≤ L.q qIdx)
    (hqLow : ComparisonLow a (L.q qIdx) n)
    (i : Fin r) (hi : ComparisonHigh a (L.x i) n)
    (hx : ∀ k : Fin r, k.val < i.val → ComparisonLow a (L.x k) n)
    (hy : ∀ k : Fin t, ComparisonLow a (L.y k) n) : False := by
  obtain ⟨u,v,hu,hv,huL,hvL,hanchor⟩ :=
    L.exists_fixed_anchors (n := n) qIdx hq (Nat.le_of_lt i.isLt) (le_rfl : t ≤ t)
      (fun z => ComparisonLow a z n) hqLow hx (fun k _ => hy k)
  have hgate (k : Fin t) (hk : k.val = i.val + (t - i.val)) : L.x i < L.y k := by
    have hkt := k.isLt
    omega
  have hrank (R : Ranking α n) : branchPosition R a b (L.x i) ≤
      branchPosition R a b u + branchPosition R a b v := by
    have hr := L.x_branchPosition_gate R i (t-i.val) hgate
    have ha := hanchor R
    have hg := (imbalance_bounds i.val t).1
    have hs : imbalance i.val t ≤ anchorBonus i.val t := Nat.le_max_right _ _
    omega
  have hc : jointComparisonCount (n := n) a (L.x i) ≤
      jointComparisonCount (n := n) a u + jointComparisonCount (n := n) a v :=
    pairCount_le_add_of_pooledBranchPositions hba hd hu hv (L.branch_label _) hrank
  unfold ComparisonLow at huL hvL
  unfold ComparisonHigh at hi
  omega

private theorem one_high_Y_false (L : Labels a b h r t)
    (hba : ¬ b ≤ a) (hd : ∀ w, w < a → w < b)
    (hh : 2 ≤ h)
    (qIdx : Fin h) (hq : ∀ k : Fin h, L.q k ≤ L.q qIdx)
    (hqLow : ComparisonLow a (L.q qIdx) n)
    (j : Fin t) (hj : ComparisonHigh a (L.y j) n)
    (hx : ∀ k : Fin r, ComparisonLow a (L.x k) n)
    (hy : ∀ k : Fin t, k.val < j.val → ComparisonLow a (L.y k) n) : False := by
  obtain ⟨u,v,hu,hv,huL,hvL,hanchor⟩ :=
    L.exists_fixed_anchors (n := n) qIdx hq (le_rfl : r ≤ r) (Nat.le_of_lt j.isLt)
      (fun z => ComparisonLow a z n) hqLow (fun k _ => hx k) hy
  have hgate (k : Fin r) (hk : k.val = j.val + (r - j.val)) : L.y j < L.x k := by
    have hkr := k.isLt
    omega
  have hrank (R : Ranking α n) : branchPosition R a b (L.y j) ≤
      branchPosition R a b u + branchPosition R a b v := by
    have hr := L.y_branchPosition_gate R j (r-j.val) hgate
    have ha := hanchor R
    have hg := (imbalance_bounds r j.val).2
    have hs : imbalance r j.val ≤ anchorBonus r j.val := Nat.le_max_right _ _
    omega
  have hc : jointComparisonCount (n := n) a (L.y j) ≤
      jointComparisonCount (n := n) a u + jointComparisonCount (n := n) a v :=
    pairCount_le_add_of_pooledBranchPositions hba hd hu hv (L.branch_label _) hrank
  unfold ComparisonLow at huL hvL
  unfold ComparisonHigh at hj
  omega

/-- Shared no-balance assembly, abstracting just the two-high obstruction. -/
theorem Labels.balanced_of_firstHigh_obstruction (L : Labels a b h r t)
    (hba : ¬ b ≤ a) (hab : ¬ a ≤ b) (hd : ∀ z, z < a → z < b)
    (hh : 2 ≤ h)
    (hmono : StrictMono (fun k : Fin h => L.q k))
    (hfirst : ∀ k : Fin h, k.val = 0 → L.q k = b)
    (hhalf : 2*jointComparisonCount (n := n) a b ≤ Nat.card (Ranking α n))
    (twoHigh : ∀ (qIdx : Fin h), (∀ k : Fin h, L.q k ≤ L.q qIdx) →
      ∀ (i : Fin r) (j : Fin t), ComparisonLow a (L.q qIdx) n →
      (∀ k : Fin r, k.val < i.val → ComparisonLow a (L.x k) n) →
      (∀ k : Fin t, k.val < j.val → ComparisonLow a (L.y k) n) →
      ¬ (ComparisonHigh a (L.x i) n ∧ ComparisonHigh a (L.y j) n)) :
    ∃ z, Branch a b z ∧ ComparisonBalanced a z n := by
  classical
  by_contra hNo
  have hb : Branch a b b := ⟨le_rfl,fun h => hab h.le⟩
  have hn (z : α) (hz : Branch a b z) : ¬ ComparisonBalanced a z n :=
    fun h => hNo ⟨z,hz,h⟩
  have hc (z : α) (hz : Branch a b z) : ComparisonLow a z n ∨ ComparisonHigh a z n :=
    notBalanced_cases (branch_ne hba hz) (hn z hz)
  have hbLow := low_of_notBalanced_and_half (branch_ne hba hb) (hn b hb) hhalf
  let qIdx : Fin h := ⟨h-1,by omega⟩
  have hq (k : Fin h) : L.q k ≤ L.q qIdx := by
    apply hmono.monotone
    change k.val ≤ h-1
    have hk := k.isLt
    omega
  have hqLow := all_prefix_low L hba hd hmono hfirst hbLow hc qIdx
  have hX := all_low_or_first_high (fun k : Fin r => ComparisonLow a (L.x k) n)
    (fun k => ComparisonHigh a (L.x k) n) (fun k => hc _ (L.branch_label _))
  have hY := all_low_or_first_high (fun k : Fin t => ComparisonLow a (L.y k) n)
    (fun k => ComparisonHigh a (L.y k) n) (fun k => hc _ (L.branch_label _))
  rcases hX with hx | ⟨i,hi,hx⟩
  · rcases hY with hy | ⟨j,hj,hy⟩
    · exact all_rails_low_false L hba hd hb hbLow qIdx hq hqLow hx hy
    · exact one_high_Y_false L hba hd hh qIdx hq hqLow j hj hx hy
  · rcases hY with hy | ⟨j,hj,hy⟩
    · exact one_high_X_false L hba hd hh qIdx hq hqLow i hi hx hy
    · exact twoHigh qIdx hq i j hqLow hx hy ⟨hi,hj⟩

/-- Integer-count statement of the written rank-only diagonal-gated
theorem. In fact the balanced comparison involves the distinguished a
and a label of the exclusive branch. No arm length cap is assumed. -/
theorem Labels.balanced_of_diagonal_gates (L : Labels a b h r t)
    (hba : ¬ b ≤ a) (hab : ¬ a ≤ b) (hd : ∀ z, z < a → z < b)
    (hh : 2 ≤ h)
    (hmono : StrictMono (fun k : Fin h => L.q k))
    (hfirst : ∀ k : Fin h, k.val = 0 → L.q k = b)
    (d e : ℕ)
    (gateX : ∀ (i : Fin r) (j : Fin t), j.val = i.val+d → L.x i < L.y j)
    (gateY : ∀ (j : Fin t) (i : Fin r), i.val = j.val+e → L.y j < L.x i)
    (hcap : max d e+2 ≤ 2*h)
    (hhalf : 2*jointComparisonCount (n := n) a b ≤ Nat.card (Ranking α n)) :
    ∃ z, Branch a b z ∧ ComparisonBalanced a z n := by
  apply L.balanced_of_firstHigh_obstruction hba hab hd hh hmono hfirst hhalf
  intro qIdx hq i j hqLow hx hy
  exact L.heads_not_both_high hba hd qIdx hq i j d e (gateX i) (gateY j) hcap hqLow hx hy

#print axioms finalCut_card_le_root_count
#print axioms Labels.balanced_of_diagonal_gates

end

end WidthThree.Diagonal

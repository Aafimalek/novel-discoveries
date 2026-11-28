/- Static delta over the verified actual diagonal-head module. -/
import DiagonalBranchHeadDraft
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Sum.Basic

namespace WidthThree.Diagonal

noncomputable section

variable {α : Type*} [PartialOrder α] [Fintype α]
variable {a b : α} {n h r t : ℕ}

/-- Prefix labels and clipped arm prefixes form disjoint parts of the
actual branch, not an auxiliary sample space for rankings. -/
private def initialInclusion {i j : ℕ} (hi : i ≤ r) (hj : j ≤ t) :
    Fin h ⊕ (Fin i ⊕ Fin j) → Fin h ⊕ (Fin r ⊕ Fin t) :=
  Sum.map id (Sum.map (Fin.castLE hi) (Fin.castLE hj))

private theorem initialInclusion_injective {i j : ℕ} (hi : i ≤ r) (hj : j ≤ t) :
    Function.Injective (initialInclusion (h := h) hi hj) := by
  unfold initialInclusion
  exact Sum.map_injective.mpr ⟨Function.injective_id, Sum.map_injective.mpr
    ⟨Fin.castLE_injective hi, Fin.castLE_injective hj⟩⟩

/-- Count initial segments at or before z in the actual ambient ranking.
The weak comparison allows one counted label to be z itself. -/
theorem Labels.initialSegments_le_branchPosition (L : Labels a b h r t)
    (R : Ranking α n) (z : α) {i j : ℕ} (hi : i ≤ r) (hj : j ≤ t)
    (hp : ∀ k : Fin h, R.rank (L.label (Sum.inl k)) ≤ R.rank z)
    (hx : ∀ k : Fin r, k.val < i → R.rank (L.x k) ≤ R.rank z)
    (hy : ∀ k : Fin t, k.val < j → R.rank (L.y k) ≤ R.rank z) :
    h+i+j ≤ branchPosition R a b z := by
  classical
  let f : Fin h ⊕ (Fin i ⊕ Fin j) → α := L.label ∘ initialInclusion hi hj
  have hf : Function.Injective f := L.inj.comp (initialInclusion_injective hi hj)
  have hbefore (w : Fin h ⊕ (Fin i ⊕ Fin j)) : R.rank (f w) ≤ R.rank z := by
    rcases w with w | w
    · exact hp w
    · rcases w with w | w
      · exact hx (Fin.castLE hi w) w.isLt
      · exact hy (Fin.castLE hj w) w.isLt
  have hbranch (w : Fin h ⊕ (Fin i ⊕ Fin j)) : Branch a b (f w) :=
    L.branch_label (initialInclusion hi hj w)
  have hs : (Finset.univ.image f) ⊆ insert z (beforeSet R z (Branch a b)) := by
    intro w hw
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hw
    by_cases he : R.rank (f v) = R.rank z
    · exact Finset.mem_insert.mpr (Or.inl (R.inj he))
    · exact Finset.mem_insert.mpr (Or.inr (mem_beforeSet.mpr
        ⟨hbranch v, lt_of_le_of_ne (hbefore v) he⟩))
  have hc := (Finset.card_le_card hs).trans (Finset.card_insert_le z _)
  rw [Finset.card_image_of_injective _ hf] at hc
  simp only [Finset.card_univ, Fintype.card_sum, Fintype.card_fin] at hc
  unfold branchPosition
  omega

abbrev Labels.q (L : Labels a b h r t) (qIdx : Fin h) : α :=
  L.label (Sum.inl qIdx)

/-- Empty low prefixes fall back to the last element of the common prefix. -/
def Labels.lowAnchorX (L : Labels a b h r t) (qIdx : Fin h)
    (i : ℕ) (hi : i ≤ r) : α :=
  if hz : i = 0 then L.q qIdx else L.x ⟨i-1, by omega⟩

def Labels.lowAnchorY (L : Labels a b h r t) (qIdx : Fin h)
    (j : ℕ) (hj : j ≤ t) : α :=
  if hz : j = 0 then L.q qIdx else L.y ⟨j-1, by omega⟩

omit [Fintype α] in
private theorem lowLeX (L : Labels a b h r t) (qIdx : Fin h)
    {i : ℕ} (hi : i ≤ r) (k : Fin r) (hk : k.val < i) :
    L.x k ≤ L.lowAnchorX qIdx i hi := by
  have hz : i ≠ 0 := by omega
  unfold Labels.lowAnchorX
  rw [dite_eq_right hz]
  apply L.x_mono.monotone
  change k.val ≤ i-1
  omega

omit [Fintype α] in
private theorem lowLeY (L : Labels a b h r t) (qIdx : Fin h)
    {j : ℕ} (hj : j ≤ t) (k : Fin t) (hk : k.val < j) :
    L.y k ≤ L.lowAnchorY qIdx j hj := by
  have hz : j ≠ 0 := by omega
  unfold Labels.lowAnchorY
  rw [dite_eq_right hz]
  apply L.y_mono.monotone
  change k.val ≤ j-1
  omega

omit [Fintype α] in
private theorem prefixLeX (L : Labels a b h r t) (qIdx : Fin h)
    (hq : ∀ k : Fin h, L.q k ≤ L.q qIdx) {i : ℕ} (hi : i ≤ r) (k : Fin h) :
    L.q k ≤ L.lowAnchorX qIdx i hi := by
  by_cases hz : i = 0
  · simpa only [Labels.lowAnchorX, dite_eq_left hz] using hq k
  · unfold Labels.lowAnchorX
    rw [dite_eq_right hz]
    exact le_of_lt (L.prefix_x k _)

omit [Fintype α] in
private theorem prefixLeY (L : Labels a b h r t) (qIdx : Fin h)
    (hq : ∀ k : Fin h, L.q k ≤ L.q qIdx) {j : ℕ} (hj : j ≤ t) (k : Fin h) :
    L.q k ≤ L.lowAnchorY qIdx j hj := by
  by_cases hz : j = 0
  · simpa only [Labels.lowAnchorY, dite_eq_left hz] using hq k
  · unfold Labels.lowAnchorY
    rw [dite_eq_right hz]
    exact le_of_lt (L.prefix_y k _)

omit [Fintype α] in
theorem Labels.lowAnchorX_mem (L : Labels a b h r t) (qIdx : Fin h) {i : ℕ} (hi : i ≤ r) :
    Branch a b (L.lowAnchorX qIdx i hi) := by
  unfold Labels.lowAnchorX
  split <;> exact L.branch_label _

omit [Fintype α] in
theorem Labels.lowAnchorY_mem (L : Labels a b h r t) (qIdx : Fin h) {j : ℕ} (hj : j ≤ t) :
    Branch a b (L.lowAnchorY qIdx j hj) := by
  unfold Labels.lowAnchorY
  split <;> exact L.branch_label _

omit [Fintype α] in
theorem Labels.lowAnchorX_property (L : Labels a b h r t) (qIdx : Fin h)
    {i : ℕ} (hi : i ≤ r) (Q : α → Prop) (hq : Q (L.q qIdx))
    (hx : ∀ k : Fin r, k.val < i → Q (L.x k)) : Q (L.lowAnchorX qIdx i hi) := by
  by_cases hz : i = 0
  · simpa only [Labels.lowAnchorX, dite_eq_left hz] using hq
  · unfold Labels.lowAnchorX
    rw [dite_eq_right hz]
    apply hx
    change i-1 < i
    omega

omit [Fintype α] in
theorem Labels.lowAnchorY_property (L : Labels a b h r t) (qIdx : Fin h)
    {j : ℕ} (hj : j ≤ t) (Q : α → Prop) (hq : Q (L.q qIdx))
    (hy : ∀ k : Fin t, k.val < j → Q (L.y k)) : Q (L.lowAnchorY qIdx j hj) := by
  by_cases hz : j = 0
  · simpa only [Labels.lowAnchorY, dite_eq_left hz] using hq
  · unfold Labels.lowAnchorY
    rw [dite_eq_right hz]
    apply hy
    change j-1 < j
    omega

theorem Labels.lowAnchorX_branchPosition (L : Labels a b h r t) (R : Ranking α n)
    (qIdx : Fin h) (hq : ∀ k : Fin h, L.q k ≤ L.q qIdx) {i : ℕ} (hi : i ≤ r) :
    h+i ≤ branchPosition R a b (L.lowAnchorX qIdx i hi) := by
  have hr := L.initialSegments_le_branchPosition R (L.lowAnchorX qIdx i hi) hi
    (Nat.zero_le t)
    (fun k => R.mono.monotone (prefixLeX L qIdx hq hi k))
    (fun k hk => R.mono.monotone (lowLeX L qIdx hi k hk))
    (fun k hk => (Nat.not_lt_zero _ hk).elim)
  simpa only [Nat.add_zero] using hr

theorem Labels.lowAnchorY_branchPosition (L : Labels a b h r t) (R : Ranking α n)
    (qIdx : Fin h) (hq : ∀ k : Fin h, L.q k ≤ L.q qIdx) {j : ℕ} (hj : j ≤ t) :
    h+j ≤ branchPosition R a b (L.lowAnchorY qIdx j hj) := by
  have hr := L.initialSegments_le_branchPosition R (L.lowAnchorY qIdx j hj)
    (Nat.zero_le r) hj
    (fun k => R.mono.monotone (prefixLeY L qIdx hq hj k))
    (fun k hk => (Nat.not_lt_zero _ hk).elim)
    (fun k hk => R.mono.monotone (lowLeY L qIdx hj k hk))
  simpa only [Nat.add_zero] using hr

/-- The X and Y last-low anchors are fixed by the data, not chosen per
ranking. Whichever is later has both initial rail segments below it. -/
theorem Labels.twoAnchor_branchPositionSum (L : Labels a b h r t) (R : Ranking α n)
    (qIdx : Fin h) (hq : ∀ k : Fin h, L.q k ≤ L.q qIdx)
    {i j : ℕ} (hi : i ≤ r) (hj : j ≤ t) :
    2*h+i+j+min i j ≤
      branchPosition R a b (L.lowAnchorX qIdx i hi) +
      branchPosition R a b (L.lowAnchorY qIdx j hj) := by
  have hsX := L.lowAnchorX_branchPosition R qIdx hq hi
  have hsY := L.lowAnchorY_branchPosition R qIdx hq hj
  rcases le_total (R.rank (L.lowAnchorX qIdx i hi)) (R.rank (L.lowAnchorY qIdx j hj)) with hxy | hyx
  · have hlater := L.initialSegments_le_branchPosition R (L.lowAnchorY qIdx j hj) hi hj
      (fun k => R.mono.monotone (prefixLeY L qIdx hq hj k))
      (fun k hk => (R.mono.monotone (lowLeX L qIdx hi k hk)).trans hxy)
      (fun k hk => R.mono.monotone (lowLeY L qIdx hj k hk))
    have hm := Nat.min_le_left i j
    omega
  · have hlater := L.initialSegments_le_branchPosition R (L.lowAnchorX qIdx i hi) hi hj
      (fun k => R.mono.monotone (prefixLeX L qIdx hq hi k))
      (fun k hk => R.mono.monotone (lowLeX L qIdx hi k hk))
      (fun k hk => (R.mono.monotone (lowLeY L qIdx hj k hk)).trans hyx)
    have hm := Nat.min_le_right i j
    omega

/-- Mirror of the checked repeated-X case. -/
theorem Labels.repeated_y_anchor_baseline (L : Labels a b h r t) (R : Ranking α n)
    (qIdx : Fin h) (hq : ∀ k : Fin h, L.q k ≤ L.q qIdx)
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ t) (hdom : i ≤ j-i) :
    2*h+i+j+anchorBonus i j ≤
      branchPosition R a b (L.lowAnchorY qIdx j hj) +
      branchPosition R a b (L.lowAnchorY qIdx j hj) := by
  have hr := L.lowAnchorY_branchPosition R qIdx hq hj
  simp only [anchorBonus, imbalance, Nat.min_eq_left hij, Nat.max_eq_right hij,
    Nat.max_eq_right hdom]
  omega

/-- Select low witnesses once and supply the universal actual rank baseline. -/
theorem Labels.exists_fixed_anchors (L : Labels a b h r t)
    (qIdx : Fin h) (hq : ∀ k : Fin h, L.q k ≤ L.q qIdx)
    {i j : ℕ} (hi : i ≤ r) (hj : j ≤ t)
    (Q : α → Prop) (hqQ : Q (L.q qIdx))
    (hxQ : ∀ k : Fin r, k.val < i → Q (L.x k))
    (hyQ : ∀ k : Fin t, k.val < j → Q (L.y k)) :
    ∃ u v, Branch a b u ∧ Branch a b v ∧ Q u ∧ Q v ∧
      ∀ R : Ranking α n, 2*h+i+j+anchorBonus i j ≤
        branchPosition R a b u + branchPosition R a b v := by
  let x := L.lowAnchorX qIdx i hi
  let y := L.lowAnchorY qIdx j hj
  have hBx : Branch a b x := L.lowAnchorX_mem qIdx hi
  have hBy : Branch a b y := L.lowAnchorY_mem qIdx hj
  have hQx : Q x := L.lowAnchorX_property qIdx hi Q hqQ hxQ
  have hQy : Q y := L.lowAnchorY_property qIdx hj Q hqQ hyQ
  by_cases hchoice : imbalance i j ≤ min i j
  · refine ⟨x, y, hBx, hBy, hQx, hQy, fun R => ?_⟩
    simpa only [anchorBonus, Nat.max_eq_left hchoice] using
      L.twoAnchor_branchPositionSum R qIdx hq hi hj
  · have hchoice' : min i j ≤ imbalance i j := by omega
    have hid := two_max_eq_sum_add_imbalance i j
    by_cases hji : j ≤ i
    · refine ⟨x, x, hBx, hBx, hQx, hQx, fun R => ?_⟩
      have hr : h+i ≤ branchPosition R a b x := L.lowAnchorX_branchPosition R qIdx hq hi
      rw [anchorBonus, Nat.max_eq_right hchoice']
      rw [Nat.max_eq_left hji] at hid
      omega
    · have hij : i ≤ j := by omega
      refine ⟨y, y, hBy, hBy, hQy, hQy, fun R => ?_⟩
      have hr : h+j ≤ branchPosition R a b y := L.lowAnchorY_branchPosition R qIdx hq hj
      rw [anchorBonus, Nat.max_eq_right hchoice']
      rw [Nat.max_eq_right hij] at hid
      omega

/-- Geometry plus certified low prefixes supplies both the fixed witnesses
and the actual head-frequency comparison. The result makes no claim about
existence of highs or how the low prefixes were selected. -/
theorem Labels.exists_anchors_frequency_heads_le (L : Labels a b h r t)
    (hba : ¬ b ≤ a) (hd : ∀ z : α, z < a → z < b)
    (qIdx : Fin h) (hq : ∀ k : Fin h, L.q k ≤ L.q qIdx)
    (i : Fin r) (j : Fin t) (d e : ℕ)
    (gateX : ∀ k : Fin t, k.val = i.val+d → L.x i < L.y k)
    (gateY : ∀ k : Fin r, k.val = j.val+e → L.y j < L.x k)
    (hcap : max d e+2 ≤ 2*h)
    (Q : α → Prop) (hqQ : Q (L.q qIdx))
    (hxQ : ∀ k : Fin r, k.val < i.val → Q (L.x k))
    (hyQ : ∀ k : Fin t, k.val < j.val → Q (L.y k)) :
    ∃ u v, Branch a b u ∧ Branch a b v ∧ Q u ∧ Q v ∧
      jointComparisonFrequency (n := n) a (L.x i) + jointComparisonFrequency (n := n) a (L.y j) ≤
        2*(jointComparisonFrequency (n := n) a u + jointComparisonFrequency (n := n) a v) := by
  obtain ⟨u,v,hu,hv,huQ,hvQ,hanchor⟩ :=
    L.exists_fixed_anchors (n := n) qIdx hq (Nat.le_of_lt i.isLt) (Nat.le_of_lt j.isLt)
      Q hqQ hxQ hyQ
  exact ⟨u,v,hu,hv,huQ,hvQ,L.frequency_heads_le hba hd i j d e gateX gateY hu hv hanchor hcap⟩

/-- Exact count version of the first-high contradiction, avoiding any
nonempty-population or rational normalization issue. -/
theorem Labels.heads_not_both_high (L : Labels a b h r t)
    (hba : ¬ b ≤ a) (hd : ∀ z : α, z < a → z < b)
    (qIdx : Fin h) (hq : ∀ k : Fin h, L.q k ≤ L.q qIdx)
    (i : Fin r) (j : Fin t) (d e : ℕ)
    (gateX : ∀ k : Fin t, k.val = i.val+d → L.x i < L.y k)
    (gateY : ∀ k : Fin r, k.val = j.val+e → L.y j < L.x k)
    (hcap : max d e+2 ≤ 2*h)
    (hqQ : 3*jointComparisonCount (n := n) a (L.q qIdx) < Nat.card (Ranking α n))
    (hxQ : ∀ k : Fin r, k.val < i.val →
      3*jointComparisonCount (n := n) a (L.x k) < Nat.card (Ranking α n))
    (hyQ : ∀ k : Fin t, k.val < j.val →
      3*jointComparisonCount (n := n) a (L.y k) < Nat.card (Ranking α n)) :
    ¬ (2*Nat.card (Ranking α n) < 3*jointComparisonCount (n := n) a (L.x i) ∧
      2*Nat.card (Ranking α n) < 3*jointComparisonCount (n := n) a (L.y j)) := by
  let Q : α → Prop := fun z => 3*jointComparisonCount (n := n) a z < Nat.card (Ranking α n)
  obtain ⟨u,v,hu,hv,huQ,hvQ,hanchor⟩ :=
    L.exists_fixed_anchors (n := n) qIdx hq (Nat.le_of_lt i.isLt) (Nat.le_of_lt j.isLt)
      Q hqQ hxQ hyQ
  have hcount := jointComparisonCount_of_branchRankSum (n := n) (x := L.x i) (y := L.y j)
    hba hd (L.branch_label _) (L.branch_label _) hu hv (fun R =>
      rankSum_le_twice_anchors h i.val j.val (max d e) _ _ _ _
        (L.head_rankSum_upper R i j d e gateX gateY) (hanchor R)
        (cap_from_small_offsets _ _ _ _ hcap))
  change 3*jointComparisonCount (n := n) a u < Nat.card (Ranking α n) at huQ
  change 3*jointComparisonCount (n := n) a v < Nat.card (Ranking α n) at hvQ
  rintro ⟨hx,hy⟩
  omega

#print axioms Labels.initialSegments_le_branchPosition
#print axioms Labels.twoAnchor_branchPositionSum
#print axioms Labels.repeated_y_anchor_baseline
#print axioms Labels.exists_fixed_anchors
#print axioms Labels.exists_anchors_frequency_heads_le
#print axioms Labels.heads_not_both_high

end

end WidthThree.Diagonal

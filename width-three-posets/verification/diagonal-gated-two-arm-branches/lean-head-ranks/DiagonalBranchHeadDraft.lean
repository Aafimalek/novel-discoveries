/-
STATIC DRAFT, not compiled.
Actual branch positions of Ranking, using only Finset cardinalities and
finite gates. This does not assume that branch and cut factorize.
-/
import DiagonalRankArithmetic
import JointBranchOrderDraft
import Mathlib.Data.Finset.Sum

namespace WidthThree.Diagonal

noncomputable section

variable {α : Type*} [PartialOrder α] [Fintype α]
variable {n h r t : ℕ} {a b : α}

/-- A disjoint finite labeling of the actual exclusive branch. -/
structure Labels (a b : α) (h r t : ℕ) where
  label : Fin h ⊕ (Fin r ⊕ Fin t) → α
  inj : Function.Injective label
  branch_iff : ∀ z, Branch a b z ↔ ∃ w, label w = z
  x_mono : StrictMono (fun i : Fin r => label (Sum.inr (Sum.inl i)))
  y_mono : StrictMono (fun j : Fin t => label (Sum.inr (Sum.inr j)))
  prefix_x : ∀ (k : Fin h) (i : Fin r), label (Sum.inl k) < label (Sum.inr (Sum.inl i))
  prefix_y : ∀ (k : Fin h) (j : Fin t), label (Sum.inl k) < label (Sum.inr (Sum.inr j))

abbrev Labels.x (L : Labels a b h r t) (i : Fin r) : α :=
  L.label (Sum.inr (Sum.inl i))

abbrev Labels.y (L : Labels a b h r t) (j : Fin t) : α :=
  L.label (Sum.inr (Sum.inr j))

omit [Fintype α] in
theorem Labels.branch_label (L : Labels a b h r t) (w : Fin h ⊕ (Fin r ⊕ Fin t)) :
    Branch a b (L.label w) :=
  (L.branch_iff _).mpr ⟨w, rfl⟩

private def belowEmbedding (m k : ℕ) : Fin (min m k) ↪ Fin m where
  toFun j := ⟨j.val, lt_of_lt_of_le j.isLt (Nat.min_le_left _ _)⟩
  inj' := by
    intro u v huv
    exact Fin.ext (congrArg (fun z : Fin m => z.val) huv)

private def below (m k : ℕ) : Finset (Fin m) :=
  Finset.univ.map (belowEmbedding m k)

@[simp] private theorem mem_below {m k : ℕ} {i : Fin m} :
    i ∈ below m k ↔ i.val < k := by
  unfold below
  constructor
  · intro hi
    obtain ⟨j, _, hji⟩ := Finset.mem_map.mp hi
    have hv := congrArg Fin.val hji
    change j.val = i.val at hv
    rw [← hv]
    exact lt_of_lt_of_le j.isLt (Nat.min_le_right _ _)
  · intro hi
    let j : Fin (min m k) := ⟨i.val, lt_min i.isLt hi⟩
    exact Finset.mem_map.mpr ⟨j, Finset.mem_univ _, Fin.ext rfl⟩

@[simp] private theorem card_below (m k : ℕ) :
    (below m k).card = min m k := by
  simp [below]

private def box (h r t cx cy : ℕ) : Finset (Fin h ⊕ (Fin r ⊕ Fin t)) :=
  (Finset.univ : Finset (Fin h)).disjSum ((below r cx).disjSum (below t cy))

@[simp] private theorem card_box (h r t cx cy : ℕ) :
    (box h r t cx cy).card = h + (min r cx + min t cy) := by
  simp [box]

/-- An actual branch rank is bounded by the number of eligible labels. -/
private theorem branchPosition_le_box (L : Labels a b h r t) (R : Ranking α n)
    {z : α} {cx cy : ℕ}
    (hx : ∀ k : Fin r, R.rank (L.x k) < R.rank z → k.val < cx)
    (hy : ∀ k : Fin t, R.rank (L.y k) < R.rank z → k.val < cy) :
    branchPosition R a b z ≤ h+cx+cy+1 := by
  classical
  have hs : beforeSet R z (Branch a b) ⊆ (box h r t cx cy).image L.label := by
    intro w hw
    obtain ⟨hwB, hwR⟩ := mem_beforeSet.mp hw
    obtain ⟨k, rfl⟩ := (L.branch_iff _).mp hwB
    refine Finset.mem_image.mpr ⟨k, ?_, rfl⟩
    rcases k with k | k
    · simp [box]
    · rcases k with k | k
      · simpa [box] using hx k hwR
      · simpa [box] using hy k hwR
  have hc := (Finset.card_le_card hs).trans (Finset.card_image_le :
    ((box h r t cx cy).image L.label).card ≤ (box h r t cx cy).card)
  rw [card_box] at hc
  have hcx := Nat.min_le_right r cx
  have hcy := Nat.min_le_right t cy
  unfold branchPosition
  omega

omit [Fintype α] in
private theorem fin_lt_of_rank_lt {s : ℕ} {f : Fin s → α} (hf : StrictMono f)
    (R : Ranking α n) {u v : Fin s} (hR : R.rank (f u) < R.rank (f v)) :
    u.val < v.val := by
  by_contra hn
  have hvu : v ≤ u := by
    change v.val ≤ u.val
    omega
  exact (not_lt_of_ge (R.mono.monotone (hf.monotone hvu))) hR

/-- The gate need only hold when its finite endpoint exists. -/
theorem Labels.x_branchPosition_gate (L : Labels a b h r t) (R : Ranking α n)
    (i : Fin r) (d : ℕ)
    (gate : ∀ j : Fin t, j.val = i.val+d → L.x i < L.y j) :
    branchPosition R a b (L.x i) ≤ h+i.val+(i.val+d)+1 := by
  apply branchPosition_le_box L R (cx := i.val) (cy := i.val+d)
  · intro k hk
    exact fin_lt_of_rank_lt L.x_mono R hk
  · intro k hk
    by_contra hn
    have hdk : i.val+d ≤ k.val := by omega
    let j : Fin t := ⟨i.val+d, lt_of_le_of_lt hdk k.isLt⟩
    have hjk : j ≤ k := hdk
    have h : L.x i < L.y k := (gate j rfl).trans_le (L.y_mono.monotone hjk)
    exact (not_lt_of_ge (le_of_lt (R.mono h))) hk

theorem Labels.y_branchPosition_gate (L : Labels a b h r t) (R : Ranking α n)
    (j : Fin t) (e : ℕ)
    (gate : ∀ i : Fin r, i.val = j.val+e → L.y j < L.x i) :
    branchPosition R a b (L.y j) ≤ h+j.val+(j.val+e)+1 := by
  -- The box bound is h + X cutoff + Y cutoff + 1; commute the cuts.
  have hup : branchPosition R a b (L.y j) ≤ h+(j.val+e)+j.val+1 := by
    apply branchPosition_le_box L R (cx := j.val+e) (cy := j.val)
    · intro k hk
      by_contra hn
      have hek : j.val+e ≤ k.val := by omega
      let i : Fin r := ⟨j.val+e, lt_of_le_of_lt hek k.isLt⟩
      have hik : i ≤ k := hek
      have hz : L.y j < L.x k := (gate i rfl).trans_le (L.x_mono.monotone hik)
      exact (not_lt_of_ge (le_of_lt (R.mono hz))) hk
    · intro k hk
      exact fin_lt_of_rank_lt L.y_mono R hk
  omega

/-- The earlier head sees only points from its two arm prefixes. -/
theorem Labels.early_head (L : Labels a b h r t) (R : Ranking α n)
    (i : Fin r) (j : Fin t) :
    branchPosition R a b (L.x i) ≤ h+i.val+j.val+1 ∨
      branchPosition R a b (L.y j) ≤ h+i.val+j.val+1 := by
  by_cases hxy : R.rank (L.x i) < R.rank (L.y j)
  · left
    apply branchPosition_le_box L R (cx := i.val) (cy := j.val)
    · intro k hk
      exact fin_lt_of_rank_lt L.x_mono R hk
    · intro k hk
      exact fin_lt_of_rank_lt L.y_mono R (hk.trans hxy)
  · have hne : R.rank (L.y j) ≠ R.rank (L.x i) := by
      intro he
      have hh : (Sum.inr (Sum.inr j) : Fin h ⊕ (Fin r ⊕ Fin t)) =
          Sum.inr (Sum.inl i) := L.inj (R.inj he)
      have hh' : (Sum.inr j : Fin r ⊕ Fin t) = Sum.inl i := Sum.inr.inj hh
      cases hh'
    have hyx := lt_of_le_of_ne (le_of_not_gt hxy) hne
    right
    apply branchPosition_le_box L R (cx := i.val) (cy := j.val)
    · intro k hk
      exact fin_lt_of_rank_lt L.x_mono R (hk.trans hyx)
    · intro k hk
      exact fin_lt_of_rank_lt L.y_mono R hk

/-- An actual finite-tail rank-sum bound, not a histogram premise. -/
theorem Labels.head_rankSum_upper (L : Labels a b h r t) (R : Ranking α n)
    (i : Fin r) (j : Fin t) (d e : ℕ)
    (gateX : ∀ k : Fin t, k.val = i.val+d → L.x i < L.y k)
    (gateY : ∀ k : Fin r, k.val = j.val+e → L.y j < L.x k) :
    branchPosition R a b (L.x i) + branchPosition R a b (L.y j) ≤
      2*h+2*(i.val+j.val)+2+max d e+imbalance i.val j.val :=
  upper_rankSum_of_one_early h i.val j.val d e _ _
    (L.x_branchPosition_gate R i d gateX) (L.y_branchPosition_gate R j e gateY)
    (L.early_head R i j)

/-- Actual lower bound for a possible repeated X-arm anchor. -/
theorem Labels.x_branchPosition_own_prefix (L : Labels a b h r t) (R : Ranking α n)
    (i : Fin r) : h+i.val+1 ≤ branchPosition R a b (L.x i) := by
  classical
  have hs : (box h r t i.val 0).image L.label ⊆ beforeSet R (L.x i) (Branch a b) := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    apply mem_beforeSet.mpr
    refine ⟨L.branch_label _, ?_⟩
    rcases w with w | w
    · exact R.mono (L.prefix_x w i)
    · rcases w with w | w
      · have hi : w.val < i.val := by simpa [box] using hw
        exact R.mono (L.x_mono hi)
      · simp [box] at hw
  have hc := Finset.card_le_card hs
  rw [Finset.card_image_of_injective _ L.inj, card_box, Nat.min_eq_right (Nat.le_of_lt i.isLt),
    Nat.min_zero, Nat.add_zero] at hc
  unfold branchPosition
  omega

/-- Supplies the anchor baseline when X's low prefix is longer and its
imbalance is at least the shorter low length. -/
theorem Labels.repeated_x_anchor_baseline (L : Labels a b h r t) (R : Ranking α n)
    (i : Fin r) (j : Fin t) (prev : Fin r)
    (hprev : prev.val+1 = i.val) (hji : j.val ≤ i.val)
    (hdiff : j.val ≤ i.val-j.val) :
    2*h+i.val+j.val+anchorBonus i.val j.val ≤
      branchPosition R a b (L.x prev) + branchPosition R a b (L.x prev) := by
  have hr := L.x_branchPosition_own_prefix R prev
  simp only [anchorBonus, imbalance, Nat.min_eq_right hji, Nat.max_eq_left hji,
    Nat.max_eq_right hdiff]
  omega

/-- Invoke the already checked comparison-frequency theorem with the
diagonal rank bound. Fixed anchor geometry is supplied in hanchor. -/
theorem Labels.frequency_heads_le (L : Labels a b h r t)
    (hba : ¬ b ≤ a) (hd : ∀ z : α, z < a → z < b)
    (i : Fin r) (j : Fin t) (d e : ℕ)
    (gateX : ∀ k : Fin t, k.val = i.val+d → L.x i < L.y k)
    (gateY : ∀ k : Fin r, k.val = j.val+e → L.y j < L.x k)
    {u v : α} (hu : Branch a b u) (hv : Branch a b v)
    (hanchor : ∀ R : Ranking α n, 2*h+i.val+j.val+anchorBonus i.val j.val ≤
      branchPosition R a b u + branchPosition R a b v)
    (hcap : max d e+2 ≤ 2*h) :
    jointComparisonFrequency (n := n) a (L.x i) + jointComparisonFrequency (n := n) a (L.y j) ≤
      2*(jointComparisonFrequency (n := n) a u + jointComparisonFrequency (n := n) a v) := by
  refine jointComparisonFrequency_of_branchRankSum (n := n) (x := L.x i) (y := L.y j)
    hba hd (L.branch_label _) (L.branch_label _) hu hv ?_
  intro R
  exact rankSum_le_twice_anchors h i.val j.val (max d e) _ _ _ _
    (L.head_rankSum_upper R i j d e gateX gateY) (hanchor R) (cap_from_small_offsets _ _ _ _ hcap)

#print axioms Labels.x_branchPosition_gate
#print axioms Labels.head_rankSum_upper
#print axioms Labels.repeated_x_anchor_baseline
#print axioms Labels.frequency_heads_le

end

end WidthThree.Diagonal

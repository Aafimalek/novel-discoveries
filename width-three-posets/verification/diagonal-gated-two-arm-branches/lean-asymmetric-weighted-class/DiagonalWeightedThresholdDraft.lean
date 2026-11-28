/- Static weighted geometry and exact first-high threshold. -/
import DiagonalAnchorsDraft
import WeightedBranchCountsDraft

namespace WidthThree.Diagonal

noncomputable section

variable {α : Type*} [PartialOrder α] [Fintype α]
variable {a b : α} {n h r t : ℕ}

/-- Multiplication-up-the-cutoff budget, keeping all quantities in Nat. -/
theorem weighted_late_head {rx ry B M c d e A : ℕ}
    (hX : rx ≤ B+d+M) (hY : ry ≤ B+e+M)
    (hEarly : rx ≤ B ∨ ry ≤ B)
    (hAnchor : B+c+M ≤ A)
    (hProduct : d*e ≤ c*(d+e)) :
    e*rx + d*ry ≤ (d+e)*A := by
  have hME : e*M ≤ (d+e)*M := Nat.mul_le_mul_right M (by omega)
  have hMD : d*M ≤ (d+e)*M := Nat.mul_le_mul_right M (by omega)
  have hlast : (d+e)*(B+c+M) ≤ (d+e)*A := Nat.mul_le_mul_left _ hAnchor
  rcases hEarly with hx | hy
  · calc
      _ ≤ e*B+d*(B+e+M) := Nat.add_le_add (Nat.mul_le_mul_left e hx) (Nat.mul_le_mul_left d hY)
      _ = (d+e)*B+d*e+d*M := by ring
      _ ≤ (d+e)*B+c*(d+e)+(d+e)*M :=
        Nat.add_le_add (Nat.add_le_add (Nat.le_refl _) hProduct) hMD
      _ = (d+e)*(B+c+M) := by ring
      _ ≤ _ := hlast
  · calc
      _ ≤ e*(B+d+M)+d*B := Nat.add_le_add (Nat.mul_le_mul_left e hX) (Nat.mul_le_mul_left d hy)
      _ = (d+e)*B+d*e+e*M := by ring
      _ ≤ (d+e)*B+c*(d+e)+(d+e)*M :=
        Nat.add_le_add (Nat.add_le_add (Nat.le_refl _) hProduct) hME
      _ = (d+e)*(B+c+M) := by ring
      _ ≤ _ := hlast

theorem Labels.weighted_head_rankSum (L : Labels a b h r t) (R : Ranking α n)
    (hh : 1 ≤ h) (i : Fin r) (j : Fin t) (d e : ℕ)
    (gateX : ∀ k : Fin t, k.val = i.val+d → L.x i < L.y k)
    (gateY : ∀ k : Fin r, k.val = j.val+e → L.y j < L.x k)
    (hProduct : d*e ≤ (h-1)*(d+e))
    (A : ℕ) (hAnchor : 2*h+i.val+j.val+anchorBonus i.val j.val ≤ A) :
    e*branchPosition R a b (L.x i) + d*branchPosition R a b (L.y j) ≤ (d+e)*A := by
  let B := h+i.val+j.val+1
  let M := anchorBonus i.val j.val
  have hGap : imbalance i.val j.val ≤ M := Nat.le_max_right _ _
  obtain ⟨hij,hji⟩ := imbalance_bounds i.val j.val
  have hx : branchPosition R a b (L.x i) ≤ B+d+M := by
    have ht := L.x_branchPosition_gate R i d gateX
    dsimp only [B]
    omega
  have hy : branchPosition R a b (L.y j) ≤ B+e+M := by
    have ht := L.y_branchPosition_gate R j e gateY
    dsimp only [B]
    omega
  have hA : B+(h-1)+M ≤ A := by
    dsimp only [B,M]
    omega
  exact weighted_late_head hx hy (L.early_head R i j) hA hProduct

theorem weighted_high_impossible {p q cx cy cu cv N : ℕ}
    (hWeight : 0 < p+q)
    (hu : 3*cu < N) (hv : 3*cv < N)
    (hx : 2*N < 3*cx) (hy : 2*N < 3*cy)
    (hCount : p*cx+q*cy ≤ (p+q)*(cu+cv)) : False := by
  have hlow : 3*(cu+cv) < 2*N := by omega
  have hh : (p+q)*(2*N) ≤ p*(3*cx)+q*(3*cy) := by
    rw [Nat.add_mul]
    exact Nat.add_le_add (Nat.mul_le_mul_left p hx.le) (Nat.mul_le_mul_left q hy.le)
  have hImpossible : (p+q)*(2*N) < (p+q)*(2*N) := by
    calc
      _ ≤ p*(3*cx)+q*(3*cy) := hh
      _ = 3*(p*cx+q*cy) := by ring
      _ ≤ 3*((p+q)*(cu+cv)) := Nat.mul_le_mul_left _ hCount
      _ = (p+q)*(3*(cu+cv)) := by ring
      _ < _ := Nat.mul_lt_mul_of_pos_left hlow hWeight
  exact (lt_irrefl _ hImpossible)

/-- Given the first highs and low initial segments, weighted rank pooling
rules out both strict highs under the product cap. -/
theorem Labels.heads_not_both_high_product (L : Labels a b h r t)
    (hba : ¬ b ≤ a) (hd : ∀ z : α, z < a → z < b) (hh : 1 ≤ h)
    (qIdx : Fin h) (hq : ∀ k : Fin h, L.q k ≤ L.q qIdx)
    (i : Fin r) (j : Fin t) (d e : ℕ)
    (gateX : ∀ k : Fin t, k.val = i.val+d → L.x i < L.y k)
    (gateY : ∀ k : Fin r, k.val = j.val+e → L.y j < L.x k)
    (hProduct : d*e ≤ (h-1)*(d+e)) (hWeight : 0 < d+e)
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
  have hCount := WeightedPool.weightedComparisonCount_of_branchRankSum (n := n)
    (x := L.x i) (y := L.y j) e d hba hd (L.branch_label _) (L.branch_label _) hu hv
    (fun R => by
      rw [Nat.add_comm e d]
      exact L.weighted_head_rankSum R hh i j d e gateX gateY hProduct _ (hanchor R))
  have hpos : 0 < e+d := by omega
  rintro ⟨hx,hy⟩
  exact weighted_high_impossible hpos huQ hvQ hx hy hCount

#print axioms weighted_late_head
#print axioms Labels.weighted_head_rankSum
#print axioms Labels.heads_not_both_high_product

end

end WidthThree.Diagonal

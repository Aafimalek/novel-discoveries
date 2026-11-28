/- Static end-to-end product-cap draft; import the local assembly delta. -/
import DiagonalBalancedDraft
import DiagonalWeightedThresholdDraft

namespace WidthThree.Diagonal

noncomputable section

variable {α : Type*} [PartialOrder α] [Fintype α]
variable {a b : α} {n h r t : ℕ}

/-- Asymmetric diagonal-gate criterion. Both zero gate offsets are
inconsistent when both arms are nonempty; empty arms are allowed. -/
theorem Labels.balanced_of_diagonal_product (L : Labels a b h r t)
    (hba : ¬ b ≤ a) (hab : ¬ a ≤ b) (hd : ∀ z, z < a → z < b)
    (hh : 2 ≤ h)
    (hmono : StrictMono (fun k : Fin h => L.q k))
    (hfirst : ∀ k : Fin h, k.val = 0 → L.q k = b)
    (d e : ℕ)
    (gateX : ∀ (i : Fin r) (j : Fin t), j.val = i.val+d → L.x i < L.y j)
    (gateY : ∀ (j : Fin t) (i : Fin r), i.val = j.val+e → L.y j < L.x i)
    (hProduct : d*e ≤ (h-1)*(d+e))
    (hhalf : 2*jointComparisonCount (n := n) a b ≤ Nat.card (Ranking α n)) :
    ∃ z, Branch a b z ∧ ComparisonBalanced a z n := by
  apply L.balanced_of_firstHigh_obstruction hba hab hd hh hmono hfirst hhalf
  intro qIdx hq i j hqLow hx hy
  by_cases hPos : 0 < d+e
  · exact L.heads_not_both_high_product hba hd (by omega) qIdx hq i j d e
      (gateX i) (gateY j) hProduct hPos hqLow hx hy
  · have hd0 : d = 0 := by omega
    have he0 : e = 0 := by omega
    have hpR : 0 < r := Nat.zero_lt_of_lt i.isLt
    have hpT : 0 < t := Nat.zero_lt_of_lt j.isLt
    let ix : Fin r := ⟨0,hpR⟩
    let jy : Fin t := ⟨0,hpT⟩
    have hxy := gateX ix jy (by simp [ix,jy,hd0])
    have hyx := gateY jy ix (by simp [ix,jy,he0])
    exact ((not_lt_of_ge hxy.le) hyx).elim

#print axioms Labels.balanced_of_diagonal_product

end

end WidthThree.Diagonal

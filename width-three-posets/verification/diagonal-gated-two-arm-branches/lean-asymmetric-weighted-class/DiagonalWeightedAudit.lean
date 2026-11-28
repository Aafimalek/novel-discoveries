/- Intended typed fresh-import audit: not yet compiled. -/
import DiagonalWeightedBalancedDraft

open WidthThree
open WidthThree.Diagonal

section
variable {α : Type*} [PartialOrder α] [Fintype α]
variable {a b : α} {n h r t : Nat}

example (L : Labels a b h r t)
    (hba : ¬ b ≤ a) (hab : ¬ a ≤ b) (hd : ∀ z, z < a → z < b)
    (hh : 2 ≤ h)
    (hmono : StrictMono (fun k : Fin h => L.q k))
    (hfirst : ∀ k : Fin h, k.val = 0 → L.q k = b)
    (d e : Nat)
    (gateX : ∀ (i : Fin r) (j : Fin t), j.val = i.val+d → L.x i < L.y j)
    (gateY : ∀ (j : Fin t) (i : Fin r), i.val = j.val+e → L.y j < L.x i)
    (hProduct : d*e ≤ (h-1)*(d+e))
    (hhalf : 2*jointComparisonCount (n := n) a b ≤ Nat.card (Ranking α n)) :
    ∃ z, Branch a b z ∧ a ≠ z ∧
      Nat.card (Ranking α n) ≤ 3*jointComparisonCount (n := n) a z ∧
      3*jointComparisonCount (n := n) a z ≤ 2*Nat.card (Ranking α n) :=
  L.balanced_of_diagonal_product hba hab hd hh hmono hfirst d e gateX gateY hProduct hhalf

end

#print axioms WidthThree.JointPool.weighted_min_le
#print axioms WidthThree.WeightedPool.weightedComparisonCount_of_branchRankSum
#print axioms Labels.heads_not_both_high_product
#print axioms Labels.balanced_of_diagonal_product

/- Intended fresh-import audit. This draft has not run. -/
import DiagonalBalancedDraft

open WidthThree
open WidthThree.Diagonal

section

variable {α : Type*} [PartialOrder α] [Fintype α]
variable {a b : α} {n h r t : Nat}

example (hba : ¬ b ≤ a) (hd : ∀ z, z < a → z < b) (hb : Branch a b b) :
    Nat.card {R : Ranking α n // finalCut a b R} ≤ jointComparisonCount (n := n) a b :=
  finalCut_card_le_root_count hba hd hb

example (L : Labels a b h r t) (R : Ranking α n)
    (hmono : StrictMono (fun k : Fin h => L.q k)) (i : Fin h) :
    branchPosition R a b (L.q i) = i.val+1 :=
  L.prefix_branchPosition R hmono i

example (L : Labels a b h r t)
    (hba : ¬ b ≤ a) (hab : ¬ a ≤ b) (hd : ∀ z, z < a → z < b)
    (hh : 2 ≤ h)
    (hmono : StrictMono (fun k : Fin h => L.q k))
    (hfirst : ∀ k : Fin h, k.val = 0 → L.q k = b)
    (d e : ℕ)
    (gateX : ∀ (i : Fin r) (j : Fin t), j.val = i.val+d → L.x i < L.y j)
    (gateY : ∀ (j : Fin t) (i : Fin r), i.val = j.val+e → L.y j < L.x i)
    (hcap : max d e+2 ≤ 2*h)
    (hhalf : 2*jointComparisonCount (n := n) a b ≤ Nat.card (Ranking α n)) :
    ∃ z, Branch a b z ∧ a ≠ z ∧
      Nat.card (Ranking α n) ≤ 3*jointComparisonCount (n := n) a z ∧
      3*jointComparisonCount (n := n) a z ≤ 2*Nat.card (Ranking α n) :=
  L.balanced_of_diagonal_gates hba hab hd hh hmono hfirst d e gateX gateY hcap hhalf

end

#print axioms finalCut_card_le_root_count
#print axioms Labels.prefix_branchPosition
#print axioms Labels.balanced_of_diagonal_gates

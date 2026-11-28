import DiagonalAnchorsDraft

open WidthThree
open WidthThree.Diagonal

section

variable {α : Type*} [PartialOrder α] [Fintype α]
variable {a b : α} {n h r t : Nat}

example (L : Labels a b h r t) (R : Ranking α n)
    (qIdx : Fin h) (hq : ∀ k : Fin h, L.q k ≤ L.q qIdx)
    {i j : Nat} (hi : i ≤ r) (hj : j ≤ t) :
    2*h+i+j+min i j ≤
      branchPosition R a b (L.lowAnchorX qIdx i hi) +
      branchPosition R a b (L.lowAnchorY qIdx j hj) :=
  L.twoAnchor_branchPositionSum R qIdx hq hi hj

example (L : Labels a b h r t) (R : Ranking α n)
    (qIdx : Fin h) (hq : ∀ k : Fin h, L.q k ≤ L.q qIdx)
    {i j : Nat} (hij : i ≤ j) (hj : j ≤ t) (hdom : i ≤ j-i) :
    2*h+i+j+anchorBonus i j ≤
      branchPosition R a b (L.lowAnchorY qIdx j hj) +
      branchPosition R a b (L.lowAnchorY qIdx j hj) :=
  L.repeated_y_anchor_baseline R qIdx hq hij hj hdom

example (L : Labels a b h r t)
    (qIdx : Fin h) (hq : ∀ k : Fin h, L.q k ≤ L.q qIdx)
    {i j : Nat} (hi : i ≤ r) (hj : j ≤ t)
    (Q : α → Prop) (hqQ : Q (L.q qIdx))
    (hxQ : ∀ k : Fin r, k.val < i → Q (L.x k))
    (hyQ : ∀ k : Fin t, k.val < j → Q (L.y k)) :
    ∃ u v, Branch a b u ∧ Branch a b v ∧ Q u ∧ Q v ∧
      ∀ R : Ranking α n, 2*h+i+j+anchorBonus i j ≤
        branchPosition R a b u + branchPosition R a b v :=
  L.exists_fixed_anchors qIdx hq hi hj Q hqQ hxQ hyQ

example (L : Labels a b h r t)
    (hba : ¬ b ≤ a) (hd : ∀ z : α, z < a → z < b)
    (qIdx : Fin h) (hq : ∀ k : Fin h, L.q k ≤ L.q qIdx)
    (i : Fin r) (j : Fin t) (d e : Nat)
    (gateX : ∀ k : Fin t, k.val = i.val+d → L.x i < L.y k)
    (gateY : ∀ k : Fin r, k.val = j.val+e → L.y j < L.x k)
    (hcap : max d e+2 ≤ 2*h)
    (hqQ : 3*jointComparisonCount (n := n) a (L.q qIdx) < Nat.card (Ranking α n))
    (hxQ : ∀ k : Fin r, k.val < i.val →
      3*jointComparisonCount (n := n) a (L.x k) < Nat.card (Ranking α n))
    (hyQ : ∀ k : Fin t, k.val < j.val →
      3*jointComparisonCount (n := n) a (L.y k) < Nat.card (Ranking α n)) :
    ¬ (2*Nat.card (Ranking α n) < 3*jointComparisonCount (n := n) a (L.x i) ∧
      2*Nat.card (Ranking α n) < 3*jointComparisonCount (n := n) a (L.y j)) :=
  L.heads_not_both_high hba hd qIdx hq i j d e gateX gateY hcap hqQ hxQ hyQ

end

#print axioms Labels.initialSegments_le_branchPosition
#print axioms Labels.twoAnchor_branchPositionSum
#print axioms Labels.repeated_y_anchor_baseline
#print axioms Labels.exists_fixed_anchors
#print axioms Labels.exists_anchors_frequency_heads_le
#print axioms Labels.heads_not_both_high

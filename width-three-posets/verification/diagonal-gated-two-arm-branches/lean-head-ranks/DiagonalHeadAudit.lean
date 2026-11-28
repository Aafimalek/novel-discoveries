import DiagonalBranchHeadDraft
open WidthThree
open WidthThree.Diagonal

section
variable {α : Type*} [PartialOrder α] [Fintype α]
variable {a b : α} {n h r t : Nat}

example (L : Labels a b h r t) (R : Ranking α n) (i : Fin r) (d : Nat)
    (gate : ∀ j : Fin t, j.val = i.val+d → L.x i < L.y j) :
    branchPosition R a b (L.x i) ≤ h+i.val+(i.val+d)+1 :=
  L.x_branchPosition_gate R i d gate

example (L : Labels a b h r t) (R : Ranking α n)
    (i : Fin r) (j : Fin t) (d e : Nat)
    (gateX : ∀ k : Fin t, k.val = i.val+d → L.x i < L.y k)
    (gateY : ∀ k : Fin r, k.val = j.val+e → L.y j < L.x k) :
    branchPosition R a b (L.x i) + branchPosition R a b (L.y j) ≤
      2*h+2*(i.val+j.val)+2+max d e+imbalance i.val j.val :=
  L.head_rankSum_upper R i j d e gateX gateY

example (L : Labels a b h r t) (R : Ranking α n)
    (i : Fin r) (j : Fin t) (u : Fin r)
    (hu : u.val+1 = i.val) (hji : j.val ≤ i.val) (hdom : j.val ≤ i.val-j.val) :
    2*h+i.val+j.val+anchorBonus i.val j.val ≤
      branchPosition R a b (L.x u) + branchPosition R a b (L.x u) :=
  L.repeated_x_anchor_baseline R i j u hu hji hdom

example (L : Labels a b h r t) (hba : ¬ b ≤ a) (hd : ∀ z : α, z < a → z < b)
    (i : Fin r) (j : Fin t) (d e : Nat)
    (gateX : ∀ k : Fin t, k.val = i.val+d → L.x i < L.y k)
    (gateY : ∀ k : Fin r, k.val = j.val+e → L.y j < L.x k)
    {u v : α} (hu : Branch a b u) (hv : Branch a b v)
    (hanchor : ∀ R : Ranking α n, 2*h+i.val+j.val+anchorBonus i.val j.val ≤
      branchPosition R a b u + branchPosition R a b v)
    (hcap : max d e+2 ≤ 2*h) :
    jointComparisonFrequency (n := n) a (L.x i) + jointComparisonFrequency (n := n) a (L.y j) ≤
      2*(jointComparisonFrequency (n := n) a u + jointComparisonFrequency (n := n) a v) :=
  L.frequency_heads_le hba hd i j d e gateX gateY hu hv hanchor hcap

end

#print axioms best_anchor_baseline
#print axioms rankSum_le_twice_anchors
#print axioms Labels.x_branchPosition_gate
#print axioms Labels.y_branchPosition_gate
#print axioms Labels.head_rankSum_upper
#print axioms Labels.repeated_x_anchor_baseline
#print axioms Labels.frequency_heads_le

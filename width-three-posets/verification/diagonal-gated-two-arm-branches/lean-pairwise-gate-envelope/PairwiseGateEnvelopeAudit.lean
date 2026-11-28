import PairwiseGateEnvelopeDraft
open WidthThree.Diagonal

example {A B C s D rx ry : Nat}
    (hx : rx ≤ C+A) (hy : ry ≤ C+B) (hearly : rx ≤ C ∨ ry ≤ C)
    (hAnchor : C+s ≤ D) (hBudget : A*B ≤ s*(A+B)) :
    B*rx+A*ry ≤ (A+B)*D :=
  pairwise_envelope_rank_le hx hy hearly hAnchor hBudget

example {A B s : Nat} (hpos : 0 < A+B) :
    (∃ p q : Nat, 0 < p+q ∧ p*A ≤ (p+q)*s ∧ q*B ≤ (p+q)*s) ↔ A*B ≤ s*(A+B) :=
  pairwise_envelope_weights_iff hpos

example {A B s : Nat} (h : A ≤ s ∨ B ≤ s) :
    A*B ≤ s*(A+B) :=
  pairwise_budget_of_one_small h

#print axioms pairwise_envelope_rank_le
#print axioms pairwise_envelope_weights_iff
#print axioms pairwise_budget_of_one_small

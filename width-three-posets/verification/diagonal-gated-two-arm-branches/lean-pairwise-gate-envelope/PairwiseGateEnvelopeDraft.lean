/- Static, standalone arithmetic draft; not yet compiled. -/
import Init

namespace WidthThree.Diagonal

/-- The local late-rank budgets A/B select fixed transposed weights B/A. -/
theorem pairwise_envelope_rank_le {A B C s D rx ry : Nat}
    (hx : rx ≤ C+A) (hy : ry ≤ C+B) (hearly : rx ≤ C ∨ ry ≤ C)
    (hAnchor : C+s ≤ D) (hBudget : A*B ≤ s*(A+B)) :
    B*rx+A*ry ≤ (A+B)*D := by
  have hb : B*rx+A*ry ≤ (A+B)*C+A*B := by
    rcases hearly with h | h
    · calc
        _ ≤ B*C+A*(C+B) := Nat.add_le_add (Nat.mul_le_mul_left B h) (Nat.mul_le_mul_left A hy)
        _ = _ := by
          rw [Nat.mul_add A C B,Nat.add_mul A B C]
          omega
    · calc
        _ ≤ B*(C+A)+A*C := Nat.add_le_add (Nat.mul_le_mul_left B hx) (Nat.mul_le_mul_left A h)
        _ = _ := by
          rw [Nat.mul_add B C A,Nat.add_mul A B C,Nat.mul_comm B A]
          omega
  calc
    _ ≤ (A+B)*C+A*B := hb
    _ ≤ (A+B)*C+s*(A+B) := Nat.add_le_add_left hBudget _
    _ = (A+B)*(C+s) := by rw [Nat.mul_add (A+B) C s,Nat.mul_comm s (A+B)]
    _ ≤ _ := Nat.mul_le_mul_left _ hAnchor

/-- Exact optimum for the two abstract late-head envelopes, not for
actual posets with more rank information. -/
theorem pairwise_envelope_weights_iff {A B s : Nat} (hpos : 0 < A+B) :
    (∃ p q : Nat, 0 < p+q ∧ p*A ≤ (p+q)*s ∧ q*B ≤ (p+q)*s) ↔
      A*B ≤ s*(A+B) := by
  constructor
  · rintro ⟨p,q,hpq,hp,hq⟩
    apply Nat.le_of_mul_le_mul_left _ hpq
    calc
      (p+q)*(A*B) = p*A*B+q*B*A := by
        rw [Nat.add_mul p q (A*B),Nat.mul_assoc p A B,Nat.mul_assoc q B A,Nat.mul_comm B A]
      _ ≤ (p+q)*s*B+(p+q)*s*A :=
        Nat.add_le_add (Nat.mul_le_mul_right B hp) (Nat.mul_le_mul_right A hq)
      _ = (p+q)*(s*(A+B)) := by
        rw [← Nat.mul_add,Nat.add_comm B A,Nat.mul_assoc]
  · intro h
    have hW : (B+A)*s = s*(A+B) := by rw [Nat.add_comm B A,Nat.mul_comm (A+B) s]
    refine ⟨B,A,by omega,?_,?_⟩
    · rw [Nat.mul_comm B A,hW]
      exact h
    · rw [hW]
      exact h

/-- One small local increment is sufficient, regardless of the other. -/
theorem pairwise_budget_of_one_small {A B s : Nat} (h : A ≤ s ∨ B ≤ s) :
    A*B ≤ s*(A+B) := by
  rcases h with hx | hy
  · exact Nat.le_trans (Nat.mul_le_mul_right B hx) (Nat.mul_le_mul_left s (by omega))
  · calc
      _ ≤ A*s := Nat.mul_le_mul_left A hy
      _ = s*A := Nat.mul_comm A s
      _ ≤ _ := Nat.mul_le_mul_left s (by omega)

#print axioms pairwise_envelope_rank_le
#print axioms pairwise_envelope_weights_iff
#print axioms pairwise_budget_of_one_small

end WidthThree.Diagonal

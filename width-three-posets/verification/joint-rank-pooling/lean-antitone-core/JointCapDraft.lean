/- Uncompiled standalone draft; no Mathlib dependency. -/
import Init

namespace WidthThree.JointPool

theorem min_add_min_le_twice {r s d e H : Nat} (h : r + s ≤ 2 * (d + e)) :
    min r H + min s H ≤ 2 * (min d H + min e H) := by
  have hcap : min r H + min s H ≤ H + H :=
    Nat.add_le_add (Nat.min_le_right r H) (Nat.min_le_right s H)
  by_cases hd : H ≤ d
  · rw [Nat.min_eq_right hd]
    omega
  · by_cases he : H ≤ e
    · rw [Nat.min_eq_right he]
      omega
    · have hd' : d ≤ H := by omega
      have he' : e ≤ H := by omega
      rw [Nat.min_eq_left hd', Nat.min_eq_left he']
      exact Nat.le_trans (Nat.add_le_add (Nat.min_le_left r H) (Nat.min_le_left s H)) h

/-- Data entries are (positive cutoff length, nonnegative weight). -/
def cappedSum (k : Nat) : List (Nat × Nat) → Nat
  | [] => 0
  | (H, w) :: layers => w * min k H + cappedSum k layers

theorem cappedSum_joint (layers : List (Nat × Nat)) {r s d e : Nat}
    (h : r + s ≤ 2 * (d + e)) :
    cappedSum r layers + cappedSum s layers ≤
      2 * (cappedSum d layers + cappedSum e layers) := by
  induction layers with
  | nil => simp [cappedSum]
  | cons hd tl ih =>
    rcases hd with ⟨H, w⟩
    have hhead : w * min r H + w * min s H ≤
        2 * (w * min d H + w * min e H) := by
      calc
        w * min r H + w * min s H = w * (min r H + min s H) :=
          (Nat.mul_add _ _ _).symm
        _ ≤ w * (2 * (min d H + min e H)) :=
          Nat.mul_le_mul_left w (min_add_min_le_twice h)
        _ = (w * 2) * (min d H + min e H) := (Nat.mul_assoc _ _ _).symm
        _ = (2 * w) * (min d H + min e H) := by rw [Nat.mul_comm w 2]
        _ = 2 * (w * (min d H + min e H)) := Nat.mul_assoc _ _ _
        _ = 2 * (w * min d H + w * min e H) :=
          congrArg (fun n => 2 * n) (Nat.mul_add _ _ _)
    simp only [cappedSum]
    omega

#print axioms min_add_min_le_twice
#print axioms cappedSum_joint

end WidthThree.JointPool

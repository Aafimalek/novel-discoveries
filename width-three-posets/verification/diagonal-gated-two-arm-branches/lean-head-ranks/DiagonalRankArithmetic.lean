/- Static draft. This file needs only the pinned Lean core; no Mathlib. -/
import Init

namespace WidthThree.Diagonal

/-- Unsigned discrepancy between the lengths of the two low prefixes. -/
def imbalance (i j : Nat) : Nat := max i j - min i j

/-- Better guaranteed bonus from choosing two arm anchors or one arm twice. -/
def anchorBonus (i j : Nat) : Nat := max (min i j) (imbalance i j)

theorem imbalance_bounds (i j : Nat) :
    i ≤ j + imbalance i j ∧ j ≤ i + imbalance i j := by
  unfold imbalance
  by_cases hij : i ≤ j
  · rw [Nat.max_eq_right hij, Nat.min_eq_left hij]
    omega
  · have hji : j ≤ i := by omega
    rw [Nat.max_eq_left hji, Nat.min_eq_right hji]
    omega

theorem two_max_eq_sum_add_imbalance (i j : Nat) :
    2 * max i j = i + j + imbalance i j := by
  unfold imbalance
  by_cases hij : i ≤ j
  · rw [Nat.max_eq_right hij, Nat.min_eq_left hij]
    omega
  · have hji : j ≤ i := by omega
    rw [Nat.max_eq_left hji, Nat.min_eq_right hji]
    omega

/-- Choose the anchors before examining the actual ranking. -/
theorem best_anchor_baseline (h i j : Nat) :
    max (2*h + i + j + min i j) (2*(h + max i j)) =
      2*h + i + j + anchorBonus i j := by
  have he := two_max_eq_sum_add_imbalance i j
  unfold anchorBonus
  by_cases hchoice : imbalance i j ≤ min i j
  · have hle : 2*(h + max i j) ≤ 2*h + i + j + min i j := by omega
    rw [Nat.max_eq_left hle, Nat.max_eq_left hchoice]
  · have hr : min i j ≤ imbalance i j := by omega
    have hle : 2*h + i + j + min i j ≤ 2*(h + max i j) := by omega
    rw [Nat.max_eq_right hle, Nat.max_eq_right hr]
    omega

/-- From the early rank bound and a late directional gate bound. -/
theorem upper_rankSum_of_one_early (h i j d e rx ry : Nat)
    (hx : rx ≤ h+i+(i+d)+1) (hy : ry ≤ h+j+(j+e)+1)
    (hearly : rx ≤ h+i+j+1 ∨ ry ≤ h+i+j+1) :
    rx + ry ≤ 2*h + 2*(i+j) + 2 + max d e + imbalance i j := by
  have hd := Nat.le_max_left d e
  have he := Nat.le_max_right d e
  obtain ⟨hij, hji⟩ := imbalance_bounds i j
  rcases hearly with h | h <;> omega

/-- Arithmetic discharger for the already formalized joint frequency rule. -/
theorem rankSum_le_twice_anchors (h i j D rx ry ru rv : Nat)
    (hupper : rx + ry ≤ 2*h+2*(i+j)+2+D+imbalance i j)
    (hanchor : 2*h+i+j+anchorBonus i j ≤ ru+rv)
    (hcap : D+imbalance i j+2 ≤ 2*h+2*anchorBonus i j) :
    rx + ry ≤ 2*(ru+rv) := by
  omega

theorem cap_from_small_offsets (h i j D : Nat)
    (hcap : D+2 ≤ 2*h) :
    D+imbalance i j+2 ≤ 2*h+2*anchorBonus i j := by
  have hbonus : imbalance i j ≤ anchorBonus i j :=
    Nat.le_max_right _ _
  omega

#print axioms best_anchor_baseline
#print axioms rankSum_le_twice_anchors

end WidthThree.Diagonal

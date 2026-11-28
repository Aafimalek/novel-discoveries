import Init

/-!
Arithmetic sublemmas for the exact-three-isolate argument. The nonlinear
expressions are over `Int` so every subtraction is ordinary subtraction.
`slackTimesSix` is the displayed upper bound for the available slack,
multiplied by six. These statements assume the paper's combinatorial bounds.
-/
namespace Frankl.ThreeIsolates

def deficitPolynomial (d g : Int) : Int :=
  (d - 4) * (g * g) + (5 * d + 8) * g + 4 * (d * (d + 1))

theorem deficit_le_three {d g : Int} (hg : 1 ≤ g)
    (hpoly : deficitPolynomial d g ≤ 0) : d ≤ 3 := by
  by_cases hd : d ≤ 3
  · exact hd
  · have h4 : 0 ≤ d - 4 := by omega
    have hd0 : 0 ≤ d := by omega
    have hd1 : 0 ≤ d + 1 := by omega
    have hg0 : 0 ≤ g := by omega
    have hgpos : 0 < g := by omega
    have hcoef : 0 < 5 * d + 8 := by omega
    have hfirst := Int.mul_nonneg h4 (Int.mul_nonneg hg0 hg0)
    have hsecond := Int.mul_pos hcoef hgpos
    have hthird := Int.mul_nonneg (by decide : (0 : Int) ≤ 4) (Int.mul_nonneg hd0 hd1)
    unfold deficitPolynomial at hpoly
    omega

def slackTimesSix (d k : Int) : Int :=
  (6 - 2 * d) * k + 3 * (d * d) - 15 * d - 18

theorem slackTimesSix_at_three (k : Int) : slackTimesSix 3 k = -36 := by
  simp [slackTimesSix]

/-- An existing fiber forces the upper bound on available slack to be nonnegative. -/
theorem deficit_le_two {d k : Int} (hd : d ≤ 3)
    (hslack : 0 ≤ slackTimesSix d k) : d ≤ 2 := by
  by_cases h : d = 3
  · subst d
    rw [slackTimesSix_at_three] at hslack
    omega
  · omega

/-- One merged signature costs `g+2`, strictly more than the available slack. -/
theorem one_signature_loss_exceeds_slack {d g k : Int} (hg : 1 ≤ g)
    (hkg : k = g + d + 1) (hd : d = 1 ∨ d = 2) :
    slackTimesSix d k < 6 * (g + 2) := by
  rcases hd with h | h
  · subst d
    unfold slackTimesSix
    omega
  · subst d
    unfold slackTimesSix
    omega

/-- The corresponding numerical fiber inequality cannot survive one merged signature. -/
theorem no_signature_loss {d g k : Int} (hg : 1 ≤ g)
    (hkg : k = g + d + 1) (hd : d = 1 ∨ d = 2)
    (hmerge : 6 * (g + 2) ≤ slackTimesSix d k) : False := by
  have hlt := one_signature_loss_exceeds_slack hg hkg hd
  omega

/-- The new both-containing members exceed the remaining fiber headroom. -/
theorem terminal_headroom {k : Int} (hk : 3 ≤ k) :
    3 * (k - 2) > k - 3 := by omega

#print axioms deficit_le_three
#print axioms slackTimesSix_at_three
#print axioms deficit_le_two
#print axioms one_signature_loss_exceeds_slack
#print axioms no_signature_loss
#print axioms terminal_headroom

end Frankl.ThreeIsolates

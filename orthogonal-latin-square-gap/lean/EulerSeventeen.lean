import LatinGap

open scoped BigOperators
open LatinGap

namespace EulerOfficers

/-- An unused label forces at least 18 placements. -/
theorem lower_bound_of_unused_label {D : Design 6} (hD : Linear D)
    (hS : Saturated D) (x : Label 6) (hx : freq D x = 0) :
    18 ≤ D.card := by
  have choose : ∀ c : Coord, ∃ i j k : Coord,
      c ≠ i ∧ c ≠ j ∧ c ≠ k ∧ i ≠ j ∧ i ≠ k ∧ j ≠ k := by decide
  obtain ⟨i, j, k, hci, hcj, hck, hij, hik, hjk⟩ := choose x.1
  obtain ⟨t, _, hh, _, _⟩ := matching_frequency_bound hD hS hx
    (fun y => Nat.zero_le (freq D y)) hci hcj hck hij hik hjk
  change 2 * 0 ^ 2 + (6 - 0) ^ 2 + (6 - 0 - t) ^ 2 ≤ 2 * D.card at hh
  norm_num at hh
  omega

/-- For the unresolved size-17 lower bound the only possible minimum label
frequencies are one or two. This is independent of the SAT encoding. -/
theorem minimum_frequency_seventeen {D : Design 6} (hD : Linear D)
    (hS : Saturated D) (hc : D.card = 17) :
    (∀ x : Label 6, 1 ≤ freq D x) ∧
      ∀ i : Coord, ∃ a : Fin 6, freq D (i, a) ≤ 2 := by
  constructor
  · intro x
    by_contra! hx
    have h := lower_bound_of_unused_label hD hS x (by omega)
    omega
  · intro i
    by_contra! hn
    have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 6)))
      (fun a _ => show 3 ≤ freq D (i,a) by have h := hn a; omega)
    rw [sum_freq, hc] at h
    norm_num at h

#print axioms lower_bound_of_unused_label
#print axioms minimum_frequency_seventeen

end EulerOfficers

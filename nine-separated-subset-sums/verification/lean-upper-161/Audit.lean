module

import NineSeparatedSubsetSums.ConwayGuyNine

open scoped BigOperators

example :
    ∃ w : Fin 9 → ℝ, (∀ i, 0 < w i) ∧ (∀ i, w i ≤ 161) ∧ (∃ i, w i = 161) ∧
      ∀ A B : Finset (Fin 9), A ≠ B →
        1 ≤ |(∑ i ∈ A, w i) - (∑ i ∈ B, w i)| :=
  NineSeparatedSubsetSums.separated_nine_upper_161

#print axioms NineSeparatedSubsetSums.separated_nine_upper_161

import NineSeparatedSubsetSums.FourPointActual

namespace NineSeparatedSubsetSums

theorem fourPointLookupPenalty_neg (T : Array ℕ) (z : ℤ) :
    fourPointLookupPenalty T (-z) = fourPointLookupPenalty T z := by
  simp [fourPointLookupPenalty]

theorem blockCharge_neg (a c : ℤ) (f : ℤ → ℤ) (sym : ∀ z, f (-z)=f z) :
    blockCharge a f (-c)=blockCharge a f c := by
  unfold blockCharge
  have e₁ : -c-a-148= -(c+a+148) := by ring
  have e₂ : -c-a+148= -(c+a-148) := by ring
  have e₃ : -c+a-148= -(c-a+148) := by ring
  have e₄ : -c+a+148= -(c-a-148) := by ring
  simp only [e₁,e₂,e₃,e₄,sym]
  ac_rfl

/-- Symmetry and the exact block-square identity reduce verification to
nonnegative centers smaller than the selected certified radius. -/
theorem blockCharge_check_from_positive_window (a lam p : ℤ) (penalty : ℤ → ℤ)
    (nonneg : ∀ z, 0 ≤ penalty z) (even : ∀ z, penalty (-z)=penalty z)
    (R : ℕ) (bound : lam ≤ 4*((R : ℤ)^2+148^2+a^2))
    (check : ∀ j : Fin R, ((j.val : ℤ)+a)%2=p →
      lam ≤ blockCharge a (fun z => z^2+penalty z) (j.val : ℤ))
    (c : ℤ) (par : (c+a)%2=p) :
    lam ≤ blockCharge a (fun z => z^2+penalty z) c := by
  have pos (d : ℤ) (hd : 0 ≤ d) (hp : (d+a)%2=p) :
      lam ≤ blockCharge a (fun z => z^2+penalty z) d := by
    by_cases h : d < (R : ℤ)
    · let j : Fin R := ⟨d.toNat, by omega⟩
      have eq : (j.val : ℤ)=d := Int.toNat_of_nonneg hd
      exact eq ▸ check j (by rwa [eq])
    · have hs : (R : ℤ)^2≤d^2 := by
        have h' := mul_nonneg (show 0 ≤ d-(R : ℤ) by omega) (show 0 ≤ d+(R : ℤ) by omega)
        nlinarith only [h']
      have pure := blockSquare_identity a d
      unfold blockCharge at pure ⊢
      linarith [nonneg (d-a-148),nonneg (d-a+148),nonneg (d+a-148),nonneg (d+a+148)]
  by_cases hc : 0≤c
  · exact pos c hc par
  · have hn := pos (-c) (by omega) (by omega : (-c+a)%2=p)
    have E := blockCharge_neg a c (fun z => z^2+penalty z) (by
      intro z
      simp [even z])
    rwa [E] at hn

#print axioms blockCharge_check_from_positive_window

end NineSeparatedSubsetSums

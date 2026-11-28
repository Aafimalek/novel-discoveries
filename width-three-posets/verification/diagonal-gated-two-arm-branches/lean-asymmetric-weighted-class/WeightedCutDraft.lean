/- Static draft: integer-valued weighted constraints on the checked cut decomposition. -/
import ConditionalBinListDraft
import Mathlib.Tactic.Ring

namespace WidthThree.JointPool

/-- A weighted head sum is dominated by the two anchors in every
capped layer, assuming domination before truncation. -/
theorem weighted_min_le {p q r s u v H : Nat}
    (h : p*r + q*s ≤ (p+q)*(u+v)) :
    p*min r H + q*min s H ≤ (p+q)*(min u H + min v H) := by
  have hcap : p*min r H + q*min s H ≤ (p+q)*H := by
    rw [Nat.add_mul]
    exact Nat.add_le_add (Nat.mul_le_mul_left p (Nat.min_le_right r H))
      (Nat.mul_le_mul_left q (Nat.min_le_right s H))
  have hraw : p*min r H + q*min s H ≤ p*r+q*s :=
    Nat.add_le_add (Nat.mul_le_mul_left p (Nat.min_le_left r H))
      (Nat.mul_le_mul_left q (Nat.min_le_left s H))
  by_cases hu : H ≤ u
  · apply hcap.trans
    rw [Nat.min_eq_right hu]
    exact Nat.mul_le_mul_left (p+q) (by omega)
  · by_cases hv : H ≤ v
    · apply hcap.trans
      rw [Nat.min_eq_right hv]
      exact Nat.mul_le_mul_left (p+q) (by omega)
    · have hu' : u ≤ H := by omega
      have hv' : v ≤ H := by omega
      rw [Nat.min_eq_left hu', Nat.min_eq_left hv']
      exact hraw.trans h

theorem cappedSum_weighted (layers : List (Nat × Nat)) {p q r s u v : Nat}
    (h : p*r + q*s ≤ (p+q)*(u+v)) :
    p*cappedSum r layers + q*cappedSum s layers ≤
      (p+q)*(cappedSum u layers + cappedSum v layers) := by
  induction layers with
  | nil => simp [cappedSum]
  | cons a ls ih =>
    rcases a with ⟨H,w⟩
    change p*(w*min r H + cappedSum r ls) + q*(w*min s H + cappedSum s ls) ≤
      (p+q)*((w*min u H + cappedSum u ls)+(w*min v H + cappedSum v ls))
    calc
      _ = w*(p*min r H+q*min s H)+(p*cappedSum r ls+q*cappedSum s ls) := by ring
      _ ≤ w*((p+q)*(min u H+min v H))+(p+q)*(cappedSum u ls+cappedSum v ls) :=
        Nat.add_le_add (Nat.mul_le_mul_left w (weighted_min_le h)) ih
      _ = _ := by ring

theorem prefixCount_weighted {p q r s u v : Nat} (bs : List Nat) (hb : binsAntitone bs)
    (h : p*r + q*s ≤ (p+q)*(u+v)) :
    p*prefixCount r bs + q*prefixCount s bs ≤
      (p+q)*(prefixCount u bs + prefixCount v bs) := by
  simp only [prefixCount_eq_cappedSum _ _ hb]
  exact cappedSum_weighted (layersOf bs) h

theorem weighted_of_prefix_step (qBins pref : Nat → Nat)
    (hzero : pref 0 = 0) (step : ∀ k, pref (k+1) = pref k + qBins k)
    (hBins : ∀ k, qBins (k+1) ≤ qBins k)
    {p q r s u v n : Nat} (hr : r ≤ n) (hs : s ≤ n) (hu : u ≤ n) (hv : v ≤ n)
    (h : p*r + q*s ≤ (p+q)*(u+v)) :
    p*pref r + q*pref s ≤ (p+q)*(pref u + pref v) := by
  let ls := seqBins qBins 0 n
  have he (k : Nat) (hk : k ≤ n) : pref k = prefixCount k ls := by
    simpa [ls,hzero] using prefix_eq_offset_seqBins qBins pref step 0 k n hk
  rw [he r hr,he s hs,he u hu,he v hv]
  exact prefixCount_weighted ls (seqBins_antitone qBins hBins 0 n) h

#print axioms weighted_min_le
#print axioms weighted_of_prefix_step

end WidthThree.JointPool

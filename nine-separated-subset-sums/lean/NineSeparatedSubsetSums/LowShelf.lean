import Mathlib.Tactic.Linarith
import Mathlib.Data.Int.Basic

namespace NineSeparatedSubsetSums

/-- No max-148 distinct-subset-sums candidate can have penultimate weight at
most 94 once the independently proved second-moment bound is known. -/
theorem lowShelfMustCollide (a b c d e f g h : ℤ)
    (apos : 0 ≤ a) (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hde : d < e) (hef : e < f) (hfg : f < g) (hgh : g < h) (hhi : h ≤ 94)
    (moment : 87381 ≤ a^2 + b^2 + c^2 + d^2 + e^2 + f^2 + g^2 + h^2 + 148^2) :
    a + d = b + c := by
  have hb0 : 0 ≤ b := by omega
  have hc0 : 0 ≤ c := by omega
  have hd0 : 0 ≤ d := by omega
  have he0 : 0 ≤ e := by omega
  have hf0 : 0 ≤ f := by omega
  have hg0 : 0 ≤ g := by omega
  have hh0 : 0 ≤ h := by omega
  have hb : b ≤ 88 := by omega
  have hc : c ≤ 89 := by omega
  have hd : d ≤ 90 := by omega
  have he : e ≤ 91 := by omega
  have hf : f ≤ 92 := by omega
  have hg : g ≤ 93 := by omega
  have hble : b^2 ≤ 88^2 := by nlinarith [mul_nonneg (show 0 ≤ 88 - b by omega) (show 0 ≤ 88 + b by omega)]
  have hcle : c^2 ≤ 89^2 := by nlinarith [mul_nonneg (show 0 ≤ 89 - c by omega) (show 0 ≤ 89 + c by omega)]
  have hdle : d^2 ≤ 90^2 := by nlinarith [mul_nonneg (show 0 ≤ 90 - d by omega) (show 0 ≤ 90 + d by omega)]
  have hele : e^2 ≤ 91^2 := by nlinarith [mul_nonneg (show 0 ≤ 91 - e by omega) (show 0 ≤ 91 + e by omega)]
  have hfle : f^2 ≤ 92^2 := by nlinarith [mul_nonneg (show 0 ≤ 92 - f by omega) (show 0 ≤ 92 + f by omega)]
  have hgle : g^2 ≤ 93^2 := by nlinarith [mul_nonneg (show 0 ≤ 93 - g by omega) (show 0 ≤ 93 + g by omega)]
  have hhle : h^2 ≤ 94^2 := by nlinarith [mul_nonneg (show 0 ≤ 94 - h by omega) (show 0 ≤ 94 + h by omega)]
  have ha : 87 ≤ a := by
    by_contra! hlt
    have hale : a^2 ≤ 86^2 := by nlinarith [mul_nonneg (show 0 ≤ 86 - a by omega) (show 0 ≤ 86 + a by omega)]
    linarith only [moment, hale, hble, hcle, hdle, hele, hfle, hgle, hhle]
  omega

#print axioms lowShelfMustCollide

end NineSeparatedSubsetSums

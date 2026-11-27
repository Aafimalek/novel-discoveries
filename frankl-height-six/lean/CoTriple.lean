import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace FranklHeightSix

variable {α : Type*} [DecidableEq α]

def UnionClosed (G : Finset (Finset α)) : Prop :=
  ∀ ⦃A B⦄, A ∈ G → B ∈ G → A ∪ B ∈ G

def NoThreeChain (G : Finset (Finset α)) : Prop :=
  ∀ ⦃A B C⦄, A ∈ G → B ∈ G → C ∈ G → A ⊂ B → B ⊂ C → False

/-- The union of a nonempty finite union-closed family is its maximum member. -/
theorem exists_top {G : Finset (Finset α)} (hU : UnionClosed G) (hNE : G.Nonempty) :
    ∃ T ∈ G, ∀ ⦃A⦄, A ∈ G → A ⊆ T := by
  let T := G.sup' hNE id
  refine ⟨T, ?_, ?_⟩
  · exact Finset.sup'_mem (G : Set (Finset α))
      (fun _ hX _ hY => hU hX hY) G hNE id (fun _ h => h)
  · intro A hA
    exact Finset.le_sup' id hA

/-- Distinct proper members of a height-two family union to the maximum. -/
theorem union_eq_top_of_ne {G : Finset (Finset α)} {T A B : Finset α}
    (hU : UnionClosed G) (hH : NoThreeChain G) (hT : T ∈ G)
    (hTop : ∀ ⦃X⦄, X ∈ G → X ⊆ T)
    (hA : A ∈ G) (hB : B ∈ G) (hAT : A ≠ T) (hAB : A ≠ B) :
    A ∪ B = T := by
  have hAT' : A ⊂ T := Finset.ssubset_iff_subset_ne.mpr ⟨hTop hA, hAT⟩
  have hBA : ¬ B ⊆ A := by
    intro h
    exact hH hB hA hT (Finset.ssubset_iff_subset_ne.mpr ⟨h, Ne.symm hAB⟩) hAT'
  have hAne : A ≠ A ∪ B := by
    intro h
    apply hBA
    simpa only [← h] using (Finset.subset_union_right : B ⊆ A ∪ B)
  by_contra hne
  exact hH hA (hU hA hB) hT
    (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_union_left, hAne⟩)
    (Finset.ssubset_iff_subset_ne.mpr ⟨hTop (hU hA hB), hne⟩)

/-- Distinct proper members have disjoint complements in the maximum. -/
theorem disjoint_complements {G : Finset (Finset α)} {T A B : Finset α}
    (hU : UnionClosed G) (hH : NoThreeChain G) (hT : T ∈ G)
    (hTop : ∀ ⦃X⦄, X ∈ G → X ⊆ T)
    (hA : A ∈ G) (hB : B ∈ G) (hAT : A ≠ T) (hAB : A ≠ B) :
    Disjoint (T \ A) (T \ B) := by
  apply Finset.disjoint_left.mpr
  intro x hxA hxB
  have hxA' := Finset.mem_sdiff.mp hxA
  have hxB' := Finset.mem_sdiff.mp hxB
  have hxU : x ∈ A ∪ B := by
    rw [union_eq_top_of_ne hU hH hT hTop hA hB hAT hAB]
    exact hxA'.1
  exact (Finset.mem_union.mp hxU).elim hxA'.2 hxB'.2

/-- A finite union-closed family of height at most two has at most
`T.card + 1` sets, where `T` is its maximum. -/
theorem card_le_top_card_add_one {G : Finset (Finset α)} {T : Finset α}
    (hU : UnionClosed G) (hH : NoThreeChain G) (hT : T ∈ G)
    (hTop : ∀ ⦃X⦄, X ∈ G → X ⊆ T) : G.card ≤ T.card + 1 := by
  classical
  have hw (A : ↥(G.erase T)) : (T \ (A : Finset α)).Nonempty := by
    have hA := Finset.mem_erase.mp A.property
    apply Finset.sdiff_nonempty.mpr
    intro h
    exact hA.1 (Finset.Subset.antisymm (hTop hA.2) h)
  let f (A : ↥(G.erase T)) : ↥T :=
    ⟨(hw A).choose, (Finset.mem_sdiff.mp (hw A).choose_spec).1⟩
  have hfmem (A : ↥(G.erase T)) : (f A : α) ∈ T \ (A : Finset α) :=
    (hw A).choose_spec
  have hf : Function.Injective f := by
    intro A B heq
    by_contra hne
    have hA := Finset.mem_erase.mp A.property
    have hB := Finset.mem_erase.mp B.property
    have hne' : (A : Finset α) ≠ (B : Finset α) := fun h => hne (Subtype.ext h)
    have hd := disjoint_complements hU hH hT hTop hA.2 hB.2 hA.1 hne'
    exact Finset.disjoint_left.mp hd (hfmem A) (by simpa only [heq] using hfmem B)
  have hcard : (G.erase T).card ≤ T.card := Finset.card_le_card_of_injective hf
  calc
    G.card = (G.erase T).card + 1 := (Finset.card_erase_add_one hT).symm
    _ ≤ T.card + 1 := Nat.add_le_add_right hcard 1

def NoSevenChain (G : Finset (Finset α)) : Prop :=
  ∀ ⦃A B C D E F H⦄, A ∈ G → B ∈ G → C ∈ G → D ∈ G →
    E ∈ G → F ∈ G → H ∈ G → A ⊂ B → B ⊂ C → C ⊂ D →
    D ⊂ E → E ⊂ F → F ⊂ H → False

/-- A down-set of a five-member chain's bottom in a height-six family has
at most `T.card + 1` members. -/
theorem card_subsets_le_of_four_extensions {G : Finset (Finset α)}
    {T D E F H : Finset α}
    (hU : UnionClosed G) (hH : NoSevenChain G)
    (hT : T ∈ G) (hD : D ∈ G) (hE : E ∈ G) (hF : F ∈ G) (hLast : H ∈ G)
    (hTD : T ⊂ D) (hDE : D ⊂ E) (hEF : E ⊂ F) (hFH : F ⊂ H) :
    (G.filter (fun A => A ⊆ T)).card ≤ T.card + 1 := by
  let L := G.filter (fun A => A ⊆ T)
  have hL (A : Finset α) : A ∈ L ↔ A ∈ G ∧ A ⊆ T := Finset.mem_filter
  have hLT : T ∈ L := (hL T).mpr ⟨hT, fun _ hx => hx⟩
  have hLU : UnionClosed L := by
    intro A B hA hB
    have ha := (hL A).mp hA
    have hb := (hL B).mp hB
    exact (hL (A ∪ B)).mpr ⟨hU ha.1 hb.1, Finset.union_subset ha.2 hb.2⟩
  have hLH : NoThreeChain L := by
    intro A B C hA hB hC hAB hBC
    have hc := (hL C).mp hC
    exact hH ((hL A).mp hA).1 ((hL B).mp hB).1 hc.1 hD hE hF hLast hAB hBC
      (Finset.ssubset_of_subset_of_ssubset hc.2 hTD) hDE hEF hFH
  exact card_le_top_card_add_one hLU hLH hLT (fun {A} hA => ((hL A).mp hA).2)

/-- Complementation inside a fixed universe strictly reverses proper inclusion. -/
theorem sdiff_ssubset_sdiff {U P Q : Finset α} (hPQ : P ⊂ Q) (hQU : Q ⊆ U) :
    U \ Q ⊂ U \ P := by
  have hPQ' := (Finset.ssubset_iff_subset_ne.mp hPQ).1
  have hs : U \ Q ⊆ U \ P := by
    intro x hx
    have hx' := Finset.mem_sdiff.mp hx
    exact Finset.mem_sdiff.mpr ⟨hx'.1, fun h => hx'.2 (hPQ' h)⟩
  obtain ⟨x, hxQ, hxP⟩ := (Finset.ssubset_iff_of_subset hPQ').mp hPQ
  exact (Finset.ssubset_iff_of_subset hs).mpr
    ⟨x, Finset.mem_sdiff.mpr ⟨hQU hxQ, hxP⟩, fun h => (Finset.mem_sdiff.mp h).2 hxQ⟩

/-- If three nested nonempty omitted sets are represented by complements,
then the avoidance fiber of a strictly larger omitted set has linear size. -/
theorem card_avoiding_le_of_three_complements {G : Finset (Finset α)}
    {U S₁ S₂ S₃ S₄ : Finset α} (hU : UnionClosed G) (hH : NoSevenChain G)
    (hTop : ∀ ⦃A⦄, A ∈ G → A ⊆ U) (hUG : U ∈ G)
    (h₁ : U \ S₁ ∈ G) (h₂ : U \ S₂ ∈ G) (h₃ : U \ S₃ ∈ G)
    (hNE₁ : S₁.Nonempty) (h₁₂ : S₁ ⊂ S₂) (h₂₃ : S₂ ⊂ S₃)
    (h₃₄ : S₃ ⊂ S₄) (h₄U : S₄ ⊆ U) :
    (G.filter (fun A => Disjoint A S₄)).card ≤ U.card - S₄.card + 1 := by
  let L := G.filter (fun A => Disjoint A S₄)
  change L.card ≤ U.card - S₄.card + 1
  have hL (A : Finset α) : A ∈ L ↔ A ∈ G ∧ Disjoint A S₄ := Finset.mem_filter
  have hLU : UnionClosed L := by
    intro A B hA hB
    have ha := (hL A).mp hA
    have hb := (hL B).mp hB
    refine (hL (A ∪ B)).mpr ⟨hU ha.1 hb.1, Finset.disjoint_left.mpr ?_⟩
    intro x hx
    exact (Finset.mem_union.mp hx).elim
      (fun h => Finset.disjoint_left.mp ha.2 h) (fun h => Finset.disjoint_left.mp hb.2 h)
  by_cases hNE : L.Nonempty
  · obtain ⟨T, hT, hMax⟩ := exists_top hLU hNE
    have hTG := (hL T).mp hT
    have hTS₄ : T ⊆ U \ S₄ := by
      intro x hx
      exact Finset.mem_sdiff.mpr ⟨hTop hTG.1 hx, Finset.disjoint_left.mp hTG.2 hx⟩
    have h₃U : S₃ ⊆ U := fun _ hx => h₄U ((Finset.ssubset_iff_subset_ne.mp h₃₄).1 hx)
    have h₂U : S₂ ⊆ U := fun _ hx => h₃U ((Finset.ssubset_iff_subset_ne.mp h₂₃).1 hx)
    have h₁U : S₁ ⊆ U := fun _ hx => h₂U ((Finset.ssubset_iff_subset_ne.mp h₁₂).1 hx)
    have hTD : T ⊂ U \ S₃ :=
      Finset.ssubset_of_subset_of_ssubset hTS₄ (sdiff_ssubset_sdiff h₃₄ h₄U)
    have hDE : U \ S₃ ⊂ U \ S₂ := sdiff_ssubset_sdiff h₂₃ h₃U
    have hEF : U \ S₂ ⊂ U \ S₁ := sdiff_ssubset_sdiff h₁₂ h₂U
    have hFH : U \ S₁ ⊂ U := by
      obtain ⟨x, hx⟩ := hNE₁
      exact (Finset.ssubset_iff_of_subset Finset.sdiff_subset).mpr
        ⟨x, h₁U hx, fun h => (Finset.mem_sdiff.mp h).2 hx⟩
    have hFilters : L = G.filter (fun A => A ⊆ T) := by
      ext A
      rw [hL A, Finset.mem_filter]
      constructor
      · intro h
        exact ⟨h.1, hMax ((hL A).mpr h)⟩
      · intro h
        refine ⟨h.1, Finset.disjoint_left.mpr ?_⟩
        intro x hx
        exact Finset.disjoint_left.mp hTG.2 (h.2 hx)
    calc
      L.card = (G.filter (fun A => A ⊆ T)).card := congrArg Finset.card hFilters
      _ ≤ T.card + 1 := card_subsets_le_of_four_extensions hU hH hTG.1
        h₃ h₂ h₁ hUG hTD hDE hEF hFH
      _ ≤ (U \ S₄).card + 1 := Nat.add_le_add_right (Finset.card_le_card hTS₄) 1
      _ = U.card - S₄.card + 1 := by rw [Finset.card_sdiff_of_subset h₄U]
  · rw [Finset.not_nonempty_iff_eq_empty.mp hNE, Finset.card_empty]
    exact Nat.zero_le _

end FranklHeightSix

#print axioms FranklHeightSix.card_le_top_card_add_one
#print axioms FranklHeightSix.card_subsets_le_of_four_extensions
#print axioms FranklHeightSix.card_avoiding_le_of_three_complements

namespace FranklHeightSix

open scoped BigOperators

variable {α : Type*} [DecidableEq α]

/-- Subsets of a complement are exactly the subsets of the universe
disjoint from the set being complemented. -/
theorem powersetCard_sdiff_eq_filter (U A : Finset α) (k : ℕ) :
    (U \ A).powersetCard k = (U.powersetCard k).filter (fun Q => Disjoint A Q) := by
  ext Q
  simp only [Finset.mem_powersetCard, Finset.mem_filter]
  constructor
  · rintro ⟨hSub, hCard⟩
    refine ⟨⟨fun _ hx => (Finset.mem_sdiff.mp (hSub hx)).1, hCard⟩, ?_⟩
    exact Finset.disjoint_right.mpr (fun {_} hx => (Finset.mem_sdiff.mp (hSub hx)).2)
  · rintro ⟨⟨hSub, hCard⟩, hDisj⟩
    exact ⟨fun _ hx => Finset.mem_sdiff.mpr ⟨hSub hx, Finset.disjoint_right.mp hDisj hx⟩, hCard⟩

private theorem sum_indicator_eq_card_filter {ι : Type*} (s : Finset ι)
    (p : ι → Prop) [DecidablePred p] :
    (∑ x ∈ s, if p x then (1 : ℕ) else 0) = (s.filter p).card := by
  rw [← Finset.sum_filter]
  simp

/-- Count pairs consisting of a member and a fixed-size set that it avoids. -/
theorem sum_choose_sdiff_card_eq_sum_avoiders (G : Finset (Finset α)) (U : Finset α)
    (k : ℕ) :
    (∑ A ∈ G, (U \ A).card.choose k) =
      ∑ Q ∈ U.powersetCard k, (G.filter (fun A => Disjoint A Q)).card := by
  calc
    (∑ A ∈ G, (U \ A).card.choose k) =
        ∑ A ∈ G, ∑ Q ∈ U.powersetCard k, if Disjoint A Q then (1 : ℕ) else 0 := by
      apply Finset.sum_congr rfl
      intro A _
      rw [sum_indicator_eq_card_filter, ← powersetCard_sdiff_eq_filter, Finset.card_powersetCard]
    _ = ∑ Q ∈ U.powersetCard k, ∑ A ∈ G, if Disjoint A Q then (1 : ℕ) else 0 :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro Q _
      exact sum_indicator_eq_card_filter G (fun A => Disjoint A Q)

theorem sum_choose_sdiff_card_le (G : Finset (Finset α)) (U : Finset α)
    (k B : ℕ) (hB : ∀ Q ∈ U.powersetCard k, (G.filter (fun A => Disjoint A Q)).card ≤ B) :
    (∑ A ∈ G, (U \ A).card.choose k) ≤ U.card.choose k * B := by
  rw [sum_choose_sdiff_card_eq_sum_avoiders]
  calc
    _ ≤ ∑ _Q ∈ U.powersetCard k, B := Finset.sum_le_sum hB
    _ = _ := by simp [Finset.card_powersetCard]

end FranklHeightSix

#print axioms FranklHeightSix.sum_choose_sdiff_card_le

namespace FranklHeightSix

open scoped BigOperators

def fallingFour (a : ℝ) : ℝ :=
  a * (a - 1) * (a - 2) * (a - 3)

def fallingFourSlope (a : ℝ) : ℝ :=
  4*a^3 - 18*a^2 + 22*a - 6

theorem fallingFour_natCast_eq {n : ℕ} (hn : 4 ≤ n) :
    fallingFour (n : ℝ) = 24 * (n.choose 4 : ℝ) := by
  have hdf : n.descFactorial 4 = (n-3)*((n-2)*((n-1)*n)) := by
    change n.descFactorial (3+1) = _
    rw [Nat.descFactorial_succ]
    change (n-3) * n.descFactorial (2+1) = _
    rw [Nat.descFactorial_succ]
    change (n-3) * ((n-2) * n.descFactorial (1+1)) = _
    rw [Nat.descFactorial_succ, Nat.descFactorial_one]
  have hnat : (n-3)*((n-2)*((n-1)*n)) = 24 * n.choose 4 := by
    rw [← hdf, Nat.descFactorial_eq_factorial_mul_choose]
    rfl
  have hc := congrArg (fun x : ℕ => (x : ℝ)) hnat
  push_cast [Nat.cast_sub (by omega : 3 ≤ n), Nat.cast_sub (by omega : 2 ≤ n),
    Nat.cast_sub (by omega : 1 ≤ n)] at hc
  unfold fallingFour
  calc
    _ = ((n : ℝ)-3)*(((n : ℝ)-2)*(((n : ℝ)-1)*(n : ℝ))) := by ring
    _ = _ := hc

theorem fallingFour_tangent {a x : ℝ} (ha : 4 ≤ a) (hx : 4 ≤ x) :
    fallingFour a + fallingFourSlope a * (x - a) ≤ fallingFour x := by
  have h₁ : 0 ≤ (2*a - 6) * x := mul_nonneg (by linarith) (by linarith)
  have h₂ : 0 ≤ a * (a - 4) := mul_nonneg (by linarith) (by linarith)
  have h₃ : 0 ≤ x^2 + (2*a - 6)*x + 3*a^2 - 12*a + 11 := by
    nlinarith [sq_nonneg x]
  have h₄ := mul_nonneg (sq_nonneg (x - a)) h₃
  have h : fallingFour x - (fallingFour a + fallingFourSlope a*(x-a)) =
      (x-a)^2 * (x^2 + (2*a - 6)*x + 3*a^2 - 12*a + 11) := by
    unfold fallingFour fallingFourSlope
    ring
  exact sub_nonneg.mp (h.symm ▸ h₄)

theorem fallingFourSlope_nonneg {a : ℝ} (ha : 4 ≤ a) : 0 ≤ fallingFourSlope a := by
  have hd : 0 ≤ a-4 := by linarith
  have h : fallingFourSlope a = 50 + 70*(a-4) + 30*(a-4)^2 + 4*(a-4)^3 := by
    unfold fallingFourSlope
    ring
  rw [h]
  exact add_nonneg
    (add_nonneg (add_nonneg (by norm_num) (mul_nonneg (by norm_num) hd))
      (mul_nonneg (by norm_num) (pow_nonneg hd _)))
    (mul_nonneg (by norm_num) (pow_nonneg hd _))

/-- The fourth-moment Jensen step, using only an explicit polynomial tangent. -/
theorem sum_fallingFour_le_of_mean_lower {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    {a : ℝ} (ha : 4 ≤ a) (hx : ∀ i ∈ s, 4 ≤ x i)
    (hm : (s.card : ℝ) * a ≤ ∑ i ∈ s, x i) :
    (s.card : ℝ) * fallingFour a ≤ ∑ i ∈ s, fallingFour (x i) := by
  have hdev : 0 ≤ ∑ i ∈ s, (x i-a) := by
    rw [Finset.sum_sub_distrib]
    simpa only [Finset.sum_const, nsmul_eq_mul] using (sub_nonneg.mpr hm)
  calc
    (s.card : ℝ) * fallingFour a
        ≤ (s.card : ℝ) * fallingFour a + fallingFourSlope a * (∑ i ∈ s, (x i-a)) :=
      le_add_of_nonneg_right (mul_nonneg (fallingFourSlope_nonneg ha) hdev)
    _ = ∑ i ∈ s, (fallingFour a + fallingFourSlope a * (x i-a)) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ i ∈ s, fallingFour (x i) :=
      Finset.sum_le_sum (fun i hi => fallingFour_tangent ha (hx i hi))

def tailQuartic (n a : ℝ) : ℝ :=
  a * (a - 1) * (a - 2) * (a - 3) - 6 * (n - 3) * (2 * a - n)

/-- A checked Taylor-expansion positivity test for the fourth-moment polynomial. -/
theorem tailQuartic_pos_of_base {n a b : ℝ} (hba : b ≤ a)
    (hZero : 0 < tailQuartic n b)
    (hOne : 0 ≤ 4*b^3 - 18*b^2 + 22*b + 30 - 12*n)
    (hTwo : 0 ≤ 6*b^2 - 18*b + 11)
    (hThree : 0 ≤ 4*b - 6) : 0 < tailQuartic n a := by
  let d := a - b
  have hd : 0 ≤ d := sub_nonneg.mpr hba
  have hform : tailQuartic n a = tailQuartic n b +
      (4*b^3 - 18*b^2 + 22*b + 30 - 12*n)*d +
      (6*b^2 - 18*b + 11)*d^2 + (4*b - 6)*d^3 + d^4 := by
    dsimp [tailQuartic, d]
    ring
  rw [hform]
  exact add_pos_of_pos_of_nonneg
    (add_pos_of_pos_of_nonneg
      (add_pos_of_pos_of_nonneg
        (add_pos_of_pos_of_nonneg hZero (mul_nonneg hOne hd))
        (mul_nonneg hTwo (pow_nonneg hd _)))
      (mul_nonneg hThree (pow_nonneg hd _)))
    (pow_nonneg hd _)

theorem tailQuartic_pos_ge_nine {n a : ℝ} (hn : 9 ≤ n) (ha : n / 2 ≤ a) :
    0 < tailQuartic n a := by
  apply tailQuartic_pos_of_base ha
  · have h0 : 0 < n / 2 := by linarith
    have h1 : 0 < n / 2 - 1 := by linarith
    have h2 : 0 < n / 2 - 2 := by linarith
    have h3 : 0 < n / 2 - 3 := by linarith
    unfold tailQuartic
    have hz : 2 * (n / 2) - n = 0 := by ring
    rw [hz, mul_zero, sub_zero]
    exact mul_pos (mul_pos (mul_pos h0 h1) h2) h3
  · by_cases hn' : n ≤ 10
    · have h : 0 ≤ n^2 * (n - 9) :=
        mul_nonneg (sq_nonneg n) (sub_nonneg.mpr hn)
      nlinarith
    · have hn0 : 0 ≤ n := by linarith
      have h10 : 0 ≤ n - 10 := by linarith
      have h : 0 ≤ n^2 * (n - 10) := mul_nonneg (sq_nonneg n) h10
      have h' : 0 ≤ n * (n - 10) := mul_nonneg hn0 h10
      nlinarith
  · have hn0 : 0 ≤ n := by linarith
    have hn6 : 0 ≤ n - 6 := by linarith
    nlinarith [mul_nonneg hn0 hn6]
  · linarith

theorem tailQuartic_pos_eight {a : ℝ} (ha : 4 ≤ a) : 0 < tailQuartic 8 a := by
  let d := a - 4
  have hd : 0 ≤ d := sub_nonneg.mpr ha
  have h : tailQuartic 8 a = 163/7 + 35*(d-1/7)^2 + 10*d^3 + d^4 := by
    dsimp [tailQuartic, d]
    ring
  rw [h]
  exact add_pos_of_pos_of_nonneg
    (add_pos_of_pos_of_nonneg
      (add_pos_of_pos_of_nonneg (by norm_num) (mul_nonneg (by norm_num) (sq_nonneg _)))
      (mul_nonneg (by norm_num) (pow_nonneg hd _)))
    (pow_nonneg hd _)

theorem tailQuartic_pos_seven {a : ℝ} (ha : 4 < a) : 0 < tailQuartic 7 a := by
  let d := a - 4
  have hd : 0 < d := sub_pos.mpr ha
  have h : tailQuartic 7 a = 2*d + 35*d^2 + 10*d^3 + d^4 := by
    dsimp [tailQuartic, d]
    ring
  rw [h]
  exact add_pos_of_pos_of_nonneg
    (add_pos_of_pos_of_nonneg
      (add_pos_of_pos_of_nonneg
        (mul_pos (by norm_num) hd) (mul_nonneg (by norm_num) (sq_nonneg _)))
      (mul_nonneg (by norm_num) (pow_nonneg hd.le _)))
    (pow_nonneg hd.le _)

theorem tailQuartic_pos_six {a : ℝ} (ha : 31 / 7 ≤ a) : 0 < tailQuartic 6 a := by
  apply tailQuartic_pos_of_base ha <;> norm_num [tailQuartic]

theorem tailQuartic_pos_five {a : ℝ} (ha : 9 / 2 ≤ a) : 0 < tailQuartic 5 a := by
  apply tailQuartic_pos_of_base ha <;> norm_num [tailQuartic]

end FranklHeightSix

#print axioms FranklHeightSix.tailQuartic_pos_ge_nine
#print axioms FranklHeightSix.tailQuartic_pos_eight
#print axioms FranklHeightSix.tailQuartic_pos_seven
#print axioms FranklHeightSix.tailQuartic_pos_six
#print axioms FranklHeightSix.tailQuartic_pos_five
#print axioms FranklHeightSix.sum_fallingFour_le_of_mean_lower
#print axioms FranklHeightSix.fallingFour_natCast_eq

namespace FranklHeightSix

open scoped BigOperators

variable {α : Type*} [DecidableEq α]

def FullCoTriple (G : Finset (Finset α)) (U : Finset α) : Prop :=
  ∀ S ⊆ U, S.card ≤ 3 → U \ S ∈ G

def frequency (G : Finset (Finset α)) (x : α) : ℕ :=
  (G.filter (fun A => x ∈ A)).card

private theorem coTriple_fiber_bound {G : Finset (Finset α)} {U Q : Finset α}
    (hU : UnionClosed G) (hH : NoSevenChain G)
    (hTop : ∀ ⦃A⦄, A ∈ G → A ⊆ U) (hUG : U ∈ G)
    (hCo : FullCoTriple G U) (hQ : Q ∈ U.powersetCard 4) :
    (G.filter (fun A => Disjoint A Q)).card ≤ U.card - 3 := by
  have hQu := (Finset.mem_powersetCard.mp hQ).1
  have hQc := (Finset.mem_powersetCard.mp hQ).2
  obtain ⟨x, hx⟩ : Q.Nonempty := Finset.card_pos.mp (by omega)
  let S₃ := Q.erase x
  have hS₃ : S₃.card = 3 := by
    have h : S₃.card + 1 = Q.card := Finset.card_erase_add_one hx
    omega
  obtain ⟨y, hy⟩ : S₃.Nonempty := Finset.card_pos.mp (by omega)
  let S₂ := S₃.erase y
  have hS₂ : S₂.card = 2 := by
    have h : S₂.card + 1 = S₃.card := Finset.card_erase_add_one hy
    omega
  obtain ⟨z, hz⟩ : S₂.Nonempty := Finset.card_pos.mp (by omega)
  let S₁ := S₂.erase z
  have hS₁ : S₁.card = 1 := by
    have h : S₁.card + 1 = S₂.card := Finset.card_erase_add_one hz
    omega
  have h₃U : S₃ ⊆ U := (Finset.erase_subset _ _).trans hQu
  have h₂U : S₂ ⊆ U := (Finset.erase_subset _ _).trans h₃U
  have h₁U : S₁ ⊆ U := (Finset.erase_subset _ _).trans h₂U
  have h := card_avoiding_le_of_three_complements hU hH hTop hUG
    (hCo S₁ h₁U (by omega)) (hCo S₂ h₂U (by omega))
    (hCo S₃ h₃U (by omega)) (Finset.card_pos.mp (by omega))
    (Finset.erase_ssubset hz) (Finset.erase_ssubset hy) (Finset.erase_ssubset hx) hQu
  have hcard := Finset.card_le_card hQu
  omega

private theorem coTriple_layer_card {G : Finset (Finset α)} {U : Finset α}
    (hTop : ∀ ⦃A⦄, A ∈ G → A ⊆ U) (hCo : FullCoTriple G U)
    {k : ℕ} (hk : k ≤ 3) :
    (G.filter (fun A => (U \ A).card = k)).card = U.card.choose k := by
  have hEq : G.filter (fun A => (U \ A).card = k) =
      (U.powersetCard k).image (fun S => U \ S) := by
    ext A
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_powersetCard]
    constructor
    · intro hA
      exact ⟨U \ A, ⟨Finset.sdiff_subset, hA.2⟩, Finset.sdiff_sdiff_eq_self (hTop hA.1)⟩
    · rintro ⟨S, ⟨hS, hkS⟩, rfl⟩
      exact ⟨hCo S hS (by omega), by rw [Finset.sdiff_sdiff_eq_self hS, hkS]⟩
  have hInj : Set.InjOn (fun S => U \ S) (U.powersetCard k : Set (Finset α)) := by
    intro S hS T hT h
    have hSU := (Finset.mem_powersetCard.mp hS).1
    have hTU := (Finset.mem_powersetCard.mp hT).1
    have h' := congrArg (fun V => U \ V) h
    simpa only [Finset.sdiff_sdiff_eq_self hSU, Finset.sdiff_sdiff_eq_self hTU] using h'
  rw [hEq, Finset.card_image_of_injOn hInj, Finset.card_powersetCard]

private theorem shallow_sum {G : Finset (Finset α)} {U : Finset α}
    (hTop : ∀ ⦃A⦄, A ∈ G → A ⊆ U) (hCo : FullCoTriple G U) (f : ℕ → ℕ) :
    (∑ A ∈ G.filter (fun A => (U \ A).card ≤ 3), f (U \ A).card) =
      ∑ j ∈ Finset.range 4, U.card.choose j * f j := by
  calc
    _ = ∑ j ∈ Finset.range 4, ∑ A ∈ G.filter (fun A => (U \ A).card = j), f j := by
      simpa only [Finset.mem_range, Nat.lt_succ_iff] using
        (Finset.sum_fiberwise_eq_sum_filter' G (Finset.range 4) (fun A => (U \ A).card) f).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_const, Nat.nsmul_eq_mul]
      exact congrArg (fun m => m * f j)
        (coTriple_layer_card hTop hCo (by have := Finset.mem_range.mp hj; omega))

private theorem shallow_card {G : Finset (Finset α)} {U : Finset α}
    (hTop : ∀ ⦃A⦄, A ∈ G → A ⊆ U) (hCo : FullCoTriple G U) :
    (G.filter (fun A => (U \ A).card ≤ 3)).card =
      1 + U.card + U.card.choose 2 + U.card.choose 3 := by
  simpa [Finset.sum_range_succ] using shallow_sum hTop hCo (fun _ => 1)

private theorem shallow_absences {G : Finset (Finset α)} {U : Finset α}
    (hTop : ∀ ⦃A⦄, A ∈ G → A ⊆ U) (hCo : FullCoTriple G U) :
    (∑ A ∈ G.filter (fun A => (U \ A).card ≤ 3), (U \ A).card) =
      U.card + U.card.choose 2 * 2 + U.card.choose 3 * 3 := by
  simpa [Finset.sum_range_succ] using shallow_sum hTop hCo id

private theorem total_absences_two_mul_ge (G : Finset (Finset α)) (U : Finset α)
    (hfreq : ∀ x ∈ U, 2 * frequency G x ≤ G.card) :
    U.card * G.card ≤ 2 * (∑ A ∈ G, (U \ A).card) := by
  have hsum : (∑ A ∈ G, (U \ A).card) =
      ∑ Q ∈ U.powersetCard 1, (G.filter (fun A => Disjoint A Q)).card := by
    simpa only [Nat.choose_one_right] using sum_choose_sdiff_card_eq_sum_avoiders G U 1
  rw [hsum, Finset.mul_sum]
  calc
    _ = ∑ _Q ∈ U.powersetCard 1, G.card := by
      simp [Finset.card_powersetCard, Nat.nsmul_eq_mul]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro Q hQ
      obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp (Finset.mem_powersetCard.mp hQ).2
      have hx : x ∈ U := (Finset.mem_powersetCard.mp hQ).1 (Finset.mem_singleton_self x)
      have hpart := Finset.card_filter_add_card_filter_not (s := G) (p := fun A => x ∈ A)
      have hf := hfreq x hx
      unfold frequency at hf
      simp only [Finset.disjoint_singleton_right]
      omega

private theorem shallow_balance (n : ℕ) (hn : 4 ≤ n) :
    (n : ℝ) * (1 + (n : ℝ) + (n.choose 2 : ℝ) + (n.choose 3 : ℝ)) -
      2 * ((n : ℝ) + (n.choose 2 : ℝ)*2 + (n.choose 3 : ℝ)*3) =
       4 * (n.choose 4 : ℝ) := by
  have h2 : n.descFactorial 2 = (n-1)*n := by
    change n.descFactorial (1+1) = _
    rw [Nat.descFactorial_succ, Nat.descFactorial_one]
  have h3 : n.descFactorial 3 = (n-2)*((n-1)*n) := by
    change n.descFactorial (2+1) = _
    rw [Nat.descFactorial_succ, h2]
  have h2' : (n-1)*n = 2 * n.choose 2 := by
    rw [← h2, Nat.descFactorial_eq_factorial_mul_choose]
    rfl
  have h3' : (n-2)*((n-1)*n) = 6 * n.choose 3 := by
    rw [← h3, Nat.descFactorial_eq_factorial_mul_choose]
    rfl
  have hc2 := congrArg (fun x : ℕ => (x : ℝ)) h2'
  have hc3 := congrArg (fun x : ℕ => (x : ℝ)) h3'
  push_cast [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_sub (by omega : 2 ≤ n)] at hc2 hc3
  have hc4 := fallingFour_natCast_eq hn
  unfold fallingFour at hc4
  have he2 : (n.choose 2 : ℝ) = ((n : ℝ)-1)*(n : ℝ)/2 := by linarith
  have he3 : (n.choose 3 : ℝ) = ((n : ℝ)-2)*(((n : ℝ)-1)*(n : ℝ))/6 := by linarith
  have he4 : (n.choose 4 : ℝ) = (n : ℝ)*((n : ℝ)-1)*((n : ℝ)-2)*((n : ℝ)-3)/24 :=
    by linarith
  rw [he2, he3, he4]
  ring

/-- Frankl's strict majority conclusion for a finite empty-set-free
union-closed family of height at most six containing all complements
of at most three points. -/
theorem fullCoTriple_majority {G : Finset (Finset α)} {U : Finset α}
    (hU : UnionClosed G) (hH : NoSevenChain G)
    (hTop : ∀ ⦃A⦄, A ∈ G → A ⊆ U) (hUG : U ∈ G)
    (hEmpty : (∅ : Finset α) ∉ G) (hCo : FullCoTriple G U) :
    ∃ x ∈ U, G.card < 2 * frequency G x := by
  by_contra! hfreq
  let n := U.card
  let Sh := G.filter (fun A => (U \ A).card ≤ 3)
  let D := G.filter (fun A => ¬ (U \ A).card ≤ 3)
  have hn4 : 4 ≤ n := by
    by_contra! hn
    have hempty := hCo U (fun _ hx => hx) (by omega : U.card ≤ 3)
    exact hEmpty (by simpa using hempty)
  have hPartC : Sh.card + D.card = G.card :=
    Finset.card_filter_add_card_filter_not (s := G) (p := fun A => (U \ A).card ≤ 3)
  have hPartS : (∑ A ∈ Sh, (U \ A).card) + (∑ A ∈ D, (U \ A).card) =
      ∑ A ∈ G, (U \ A).card :=
    Finset.sum_filter_add_sum_filter_not G (fun A => (U \ A).card ≤ 3)
      (fun A => (U \ A).card)
  have hShC : Sh.card = 1 + n + n.choose 2 + n.choose 3 := shallow_card hTop hCo
  have hShS : (∑ A ∈ Sh, (U \ A).card) = n + n.choose 2 * 2 + n.choose 3 * 3 :=
    shallow_absences hTop hCo
  have hTotal : n * G.card ≤ 2 * (∑ A ∈ G, (U \ A).card) :=
    total_absences_two_mul_ge G U hfreq
  have hGpow : G.card + 1 ≤ 2^n := by
    have hSub : G ⊆ U.powerset.erase ∅ := by
      intro A hA
      exact Finset.mem_erase.mpr
        ⟨fun e => hEmpty (e ▸ hA), Finset.mem_powerset.mpr (hTop hA)⟩
    have hcard := Finset.card_le_card hSub
    have hE := Finset.card_erase_add_one
      (Finset.mem_powerset.mpr (Finset.empty_subset U) : (∅ : Finset α) ∈ U.powerset)
    rw [Finset.card_powerset] at hE
    change (U.powerset.erase ∅).card + 1 = 2^n at hE
    omega
  have hDc : D.card ≤ 2^n - 1 - (1+n+n.choose 2+n.choose 3) := by omega
  let K : ℝ := n.choose 4
  have hK : 0 < K := by
    dsimp [K]
    exact_mod_cast Nat.choose_pos hn4
  have hShC' : (Sh.card : ℝ) = 1 + (n:ℝ) + (n.choose 2:ℝ) + (n.choose 3:ℝ) := by
    exact_mod_cast hShC
  have hShS' : (∑ A ∈ Sh, ((U \ A).card : ℝ)) =
      (n:ℝ) + (n.choose 2:ℝ)*2 + (n.choose 3:ℝ)*3 := by
    have h := congrArg (fun x : ℕ => (x : ℝ)) hShS
    simpa only [Nat.cast_sum, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using h
  have hPartC' : (Sh.card : ℝ) + (D.card : ℝ) = (G.card : ℝ) := by exact_mod_cast hPartC
  have hPartS' : (∑ A ∈ Sh, ((U \ A).card : ℝ)) + (∑ A ∈ D, ((U \ A).card : ℝ)) =
      ∑ A ∈ G, ((U \ A).card : ℝ) := by
    have h := congrArg (fun x : ℕ => (x : ℝ)) hPartS
    simpa only [Nat.cast_sum, Nat.cast_add] using h
  have hTotal' : (n:ℝ)*(G.card:ℝ) ≤ 2*(∑ A ∈ G, ((U \ A).card:ℝ)) := by
    have h := (Nat.cast_le (α := ℝ)).2 hTotal
    simpa only [Nat.cast_sum, Nat.cast_mul, Nat.cast_ofNat] using h
  have hBalance : (n:ℝ)*(Sh.card:ℝ) - 2*(∑ A ∈ Sh, ((U \ A).card:ℝ)) = 4*K := by
    rw [hShC', hShS']
    exact shallow_balance n hn4
  have hDeep : (n:ℝ)*(D.card:ℝ) + 4*K ≤ 2*(∑ A ∈ D, ((U \ A).card:ℝ)) := by
    rw [← hPartC', mul_add, ← hPartS', mul_add] at hTotal'
    nlinarith only [hTotal', hBalance]
  have hD : 0 < (D.card:ℝ) := by
    by_contra! h
    have hz : (D.card:ℝ) = 0 := le_antisymm h (by positivity)
    have hz' : D.card = 0 := by exact_mod_cast hz
    have hsum : (∑ A ∈ D, ((U \ A).card:ℝ)) = 0 := by
      rw [Finset.card_eq_zero.mp hz', Finset.sum_empty]
    rw [hz, mul_zero, zero_add, hsum, mul_zero] at hDeep
    linarith
  let a : ℝ := (n:ℝ)/2 + 2*K/(D.card:ℝ)
  have hRel : (D.card:ℝ)*(2*a-(n:ℝ)) = 4*K := by
    dsimp [a]
    field_simp [ne_of_gt hD]
    <;> ring
  have hMean : (D.card:ℝ)*a ≤ ∑ A ∈ D, ((U \ A).card:ℝ) := by
    nlinarith only [hRel, hDeep]
  have haHalf : (n:ℝ)/2 ≤ a := le_add_of_nonneg_right (by positivity)
  have ha : 4 ≤ a ∧ 0 < tailQuartic (n:ℝ) a := by
    by_cases hn9 : 9 ≤ n
    · have hn9' : (9:ℝ) ≤ n := by exact_mod_cast hn9
      exact ⟨by linarith, tailQuartic_pos_ge_nine hn9' haHalf⟩
    · have hnCases : n=4 ∨ n=5 ∨ n=6 ∨ n=7 ∨ n=8 := by omega
      rcases hnCases with hn | hn | hn | hn | hn
      · have hd : D.card ≤ 0 := by simpa [hn, Nat.choose] using hDc
        have hd' : (D.card:ℝ) ≤ 0 := by exact_mod_cast hd
        exact False.elim ((not_le_of_gt hD) hd')
      · have hn' : (n:ℝ)=5 := by exact_mod_cast hn
        have hd : D.card ≤ 5 := by simpa [hn, Nat.choose] using hDc
        have hd' : (D.card:ℝ) ≤ 5 := by exact_mod_cast hd
        have hk : K=5 := by norm_num [K, hn, Nat.choose]
        have hdiv : (2:ℝ) ≤ 2*K/(D.card:ℝ) :=
          (le_div_iff₀ hD).mpr (by linarith)
        have hmin : 9/2 ≤ a := by dsimp [a]; linarith
        exact ⟨by linarith, by rw [hn']; exact tailQuartic_pos_five hmin⟩
      · have hn' : (n:ℝ)=6 := by exact_mod_cast hn
        have hd : D.card ≤ 21 := by simpa [hn, Nat.choose] using hDc
        have hd' : (D.card:ℝ) ≤ 21 := by exact_mod_cast hd
        have hk : K=15 := by norm_num [K, hn, Nat.choose]
        have hdiv : (10/7:ℝ) ≤ 2*K/(D.card:ℝ) :=
          (le_div_iff₀ hD).mpr (by linarith)
        have hmin : 31/7 ≤ a := by dsimp [a]; linarith
        exact ⟨by linarith, by rw [hn']; exact tailQuartic_pos_six hmin⟩
      · have hn' : (n:ℝ)=7 := by exact_mod_cast hn
        have hd : D.card ≤ 63 := by simpa [hn, Nat.choose] using hDc
        have hd' : (D.card:ℝ) ≤ 63 := by exact_mod_cast hd
        have hk : K=35 := by norm_num [K, hn, Nat.choose]
        have hdiv : (1:ℝ) ≤ 2*K/(D.card:ℝ) :=
          (le_div_iff₀ hD).mpr (by linarith)
        have hmin : 4 < a := by dsimp [a]; linarith
        exact ⟨hmin.le, by rw [hn']; exact tailQuartic_pos_seven hmin⟩
      · have hn' : (n:ℝ)=8 := by exact_mod_cast hn
        have hmin : 4 ≤ a := by linarith
        exact ⟨hmin, by rw [hn']; exact tailQuartic_pos_eight hmin⟩
  have hFour : ∀ A ∈ D, 4 ≤ (U \ A).card := by
    intro A hA
    have h := (Finset.mem_filter.mp hA).2
    omega
  have hFour' : ∀ A ∈ D, (4:ℝ) ≤ ((U \ A).card:ℝ) := by
    intro A hA
    exact_mod_cast hFour A hA
  have hMoment := sum_fallingFour_le_of_mean_lower D
    (fun A => ((U \ A).card:ℝ)) ha.1 hFour' hMean
  have hMomentEq :
      (∑ A ∈ D, fallingFour ((U \ A).card:ℝ)) =
      24 * ∑ A ∈ D, ((U \ A).card.choose 4:ℝ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun A hA => fallingFour_natCast_eq (hFour A hA))
  have hCap : (∑ A ∈ D, (U \ A).card.choose 4) ≤ n.choose 4 * (n-3) := by
    apply sum_choose_sdiff_card_le D U 4 (n-3)
    intro Q hQ
    have hDG : D ⊆ G := fun A hA => (Finset.mem_filter.mp hA).1
    calc
      _ ≤ (G.filter (fun A => Disjoint A Q)).card :=
        Finset.card_le_card (Finset.filter_subset_filter _ hDG)
      _ ≤ n-3 := coTriple_fiber_bound hU hH hTop hUG hCo hQ
  have hCap' : (∑ A ∈ D, ((U \ A).card.choose 4:ℝ)) ≤ K*((n:ℝ)-3) := by
    have h := (Nat.cast_le (α := ℝ)).2 hCap
    simpa only [K, Nat.cast_sum, Nat.cast_mul, Nat.cast_sub (by omega : 3 ≤ n),
      Nat.cast_ofNat] using h
  have hLast : (D.card:ℝ) * tailQuartic (n:ℝ) a ≤ 0 := by
    have hm : (D.card:ℝ)*fallingFour a ≤ 24*K*((n:ℝ)-3) := by
      rw [hMomentEq] at hMoment
      exact hMoment.trans (by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left hCap' (by norm_num))
    have hForm : (D.card:ℝ) * tailQuartic (n:ℝ) a =
        (D.card:ℝ)*fallingFour a - 6*((n:ℝ)-3)*((D.card:ℝ)*(2*a-(n:ℝ))) := by
      unfold tailQuartic fallingFour
      ring
    rw [hForm, hRel]
    nlinarith only [hm]
  exact (not_le_of_gt (mul_pos hD ha.2)) hLast

end FranklHeightSix

#print axioms FranklHeightSix.fullCoTriple_majority

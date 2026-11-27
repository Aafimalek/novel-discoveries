import Mathlib

namespace NineSeparatedSubsetSums

def InSlab (c M s : ℝ) : Prop := c - M ≤ s ∧ s ≤ c + M

/-- A walk that exhausts two lists of required moves while keeping every
intermediate score in the interval centered at c with radius M. -/
inductive SlabWalk (c M : ℝ) : List ℝ → List ℝ → ℝ → Prop
  | stop {s : ℝ} : InSlab c M s → SlabWalk c M [] [] s
  | up {s a : ℝ} {P N : List ℝ} :
      InSlab c M s → SlabWalk c M P N (s + a) → SlabWalk c M (a :: P) N s
  | down {s a : ℝ} {P N : List ℝ} :
      InSlab c M s → SlabWalk c M P N (s - a) → SlabWalk c M P (a :: N) s

/-- The numerical core of slab connectivity: if both kinds of moves are
available, add on the lower half or subtract on the upper half. Once only
one kind remains, move monotonically to the endpoint. -/
theorem slabWalk_exists (c M : ℝ) (P N : List ℝ) (s : ℝ)
    (hP : ∀ a ∈ P, 0 ≤ a ∧ a ≤ M)
    (hN : ∀ a ∈ N, 0 ≤ a ∧ a ≤ M)
    (hs : InSlab c M s)
    (ht : InSlab c M (s + P.sum - N.sum)) :
    SlabWalk c M P N s := by
  cases P with
  | nil =>
    cases N with
    | nil => exact SlabWalk.stop hs
    | cons b N =>
      have hb := hN b (by simp)
      have hN' : ∀ x ∈ N, 0 ≤ x ∧ x ≤ M := fun x hx => hN x (by simp [hx])
      have hNsum : 0 ≤ N.sum := List.sum_nonneg (fun x hx => (hN' x hx).1)
      have ht' : InSlab c M (s - b + ([] : List ℝ).sum - N.sum) := by
        convert ht using 1 <;> simp only [List.sum_cons, List.sum_nil] <;> ring
      have hs' : InSlab c M (s - b) := by
        obtain ⟨hlo, hhi⟩ := hs
        obtain ⟨hlo', _⟩ := ht'
        simp only [List.sum_nil] at hlo'
        exact ⟨by linarith, by linarith [hb.1]⟩
      exact SlabWalk.down hs (slabWalk_exists c M [] N (s - b) hP hN' hs' ht')
  | cons a P =>
    have ha := hP a (by simp)
    have hP' : ∀ x ∈ P, 0 ≤ x ∧ x ≤ M := fun x hx => hP x (by simp [hx])
    cases N with
    | nil =>
      have hPsum : 0 ≤ P.sum := List.sum_nonneg (fun x hx => (hP' x hx).1)
      have ht' : InSlab c M (s + a + P.sum - ([] : List ℝ).sum) := by
        convert ht using 1 <;> simp only [List.sum_cons] <;> ring
      have hs' : InSlab c M (s + a) := by
        obtain ⟨hlo, _⟩ := hs
        obtain ⟨_, hhi'⟩ := ht'
        simp only [List.sum_nil] at hhi'
        exact ⟨by linarith [ha.1], by linarith⟩
      exact SlabWalk.up hs (slabWalk_exists c M P [] (s + a) hP' hN hs' ht')
    | cons b N =>
      by_cases hmid : s ≤ c
      · have hs' : InSlab c M (s + a) := by
          exact ⟨by linarith [hs.1, ha.1], by linarith [ha.2]⟩
        have ht' : InSlab c M (s + a + P.sum - (b :: N).sum) := by
          convert ht using 1 <;> simp only [List.sum_cons] <;> ring
        exact SlabWalk.up hs
          (slabWalk_exists c M P (b :: N) (s + a) hP' hN hs' ht')
      · have hb := hN b (by simp)
        have hs' : InSlab c M (s - b) := by
          exact ⟨by linarith [lt_of_not_ge hmid, hb.2], by linarith [hs.2, hb.1]⟩
        have ht' : InSlab c M (s - b + (a :: P).sum - N.sum) := by
          convert ht using 1 <;> simp only [List.sum_cons] <;> ring
        have hN' : ∀ x ∈ N, 0 ≤ x ∧ x ≤ M := fun x hx => hN x (by simp [hx])
        exact SlabWalk.down hs
          (slabWalk_exists c M (a :: P) N (s - b) hP hN' hs' ht')
termination_by P.length + N.length
decreasing_by all_goals simp_wf <;> omega

#print axioms slabWalk_exists

end NineSeparatedSubsetSums

import NineSeparatedSubsetSums.Cube

namespace NineSeparatedSubsetSums

set_option maxHeartbeats 0
set_option maxRecDepth 8192

/-- The certified numerical profiles for dimensions zero through eight.
In dimension nine, only the entry at cardinality 158 is needed. -/
def profile (d m : ℕ) : ℕ :=
  match d with
  | 0 => (#[0, 1] : Array ℕ)[m]?.getD 0
  | 1 => (#[0, 2, 2] : Array ℕ)[m]?.getD 0
  | 2 => (#[0, 3, 4, 4, 4] : Array ℕ)[m]?.getD 0
  | 3 => (#[0, 4, 6, 7, 7, 8, 8, 8, 8] : Array ℕ)[m]?.getD 0
  | 4 => (#[0, 5, 8, 10, 11, 11, 13, 14, 14, 15, 15, 15, 16, 16, 16, 16, 16] : Array ℕ)[m]?.getD 0
  | 5 => (#[0, 6, 10, 13, 15, 16, 16, 19, 21, 22, 22, 24, 25, 25, 26, 26, 26, 28, 29, 29, 30, 30, 30, 31, 31, 31, 31, 32, 32, 32, 32, 32, 32] : Array ℕ)[m]?.getD 0
  | 6 => (#[0, 7, 12, 16, 19, 21, 22, 22, 26, 29, 31, 32, 32, 35, 37, 38, 38, 40, 41, 41, 42, 42, 42, 45, 47, 48, 48, 50, 51, 51, 52, 52, 52, 54, 55, 55, 56, 56, 56, 57, 57, 57, 57, 59, 60, 60, 61, 61, 61, 62, 62, 62, 62, 63, 63, 63, 63, 63, 64, 64, 64, 64, 64, 64, 64] : Array ℕ)[m]?.getD 0
  | 7 => (#[0, 8, 14, 19, 23, 26, 28, 29, 29, 34, 38, 41, 43, 44, 44, 48, 51, 53, 54, 54, 57, 59, 60, 60, 62, 63, 63, 64, 64, 64, 68, 71, 73, 74, 74, 77, 79, 80, 80, 82, 83, 83, 84, 84, 84, 87, 89, 90, 90, 92, 93, 93, 94, 94, 94, 96, 97, 97, 98, 98, 98, 99, 99, 99, 99, 102, 104, 105, 105, 107, 108, 108, 109, 109, 109, 111, 112, 112, 113, 113, 113, 114, 114, 114, 114, 116, 117, 117, 118, 118, 118, 119, 119, 119, 119, 120, 120, 120, 120, 120, 122, 123, 123, 124, 124, 124, 125, 125, 125, 125, 126, 126, 126, 126, 126, 127, 127, 127, 127, 127, 127, 128, 128, 128, 128, 128, 128, 128, 128] : Array ℕ)[m]?.getD 0
  | 8 => (#[0, 9, 16, 22, 27, 31, 34, 36, 37, 37, 43, 48, 52, 55, 57, 58, 58, 63, 67, 70, 72, 73, 73, 77, 80, 82, 83, 83, 86, 88, 89, 89, 91, 92, 92, 93, 93, 93, 98, 102, 105, 107, 108, 108, 112, 115, 117, 118, 118, 121, 123, 124, 124, 126, 127, 127, 128, 128, 128, 132, 135, 137, 138, 138, 141, 143, 144, 144, 146, 147, 147, 148, 148, 148, 151, 153, 154, 154, 156, 157, 157, 158, 158, 158, 160, 161, 161, 162, 162, 162, 163, 163, 163, 163, 167, 170, 172, 173, 173, 176, 178, 179, 179, 181, 182, 182, 183, 183, 183, 186, 188, 189, 189, 191, 192, 192, 193, 193, 193, 195, 196, 196, 197, 197, 197, 198, 198, 198, 198, 201, 203, 204, 204, 206, 207, 207, 208, 208, 208, 210, 211, 211, 212, 212, 212, 213, 213, 213, 213, 215, 216, 216, 217, 217, 217, 218, 218, 218, 218, 219, 219, 219, 219, 219, 222, 224, 225, 225, 227, 228, 228, 229, 229, 229, 231, 232, 232, 233, 233, 233, 234, 234, 234, 234, 236, 237, 237, 238, 238, 238, 239, 239, 239, 239, 240, 240, 240, 240, 240, 242, 243, 243, 244, 244, 244, 245, 245, 245, 245, 246, 246, 246, 246, 246, 247, 247, 247, 247, 247, 247, 249, 250, 250, 251, 251, 251, 252, 252, 252, 252, 253, 253, 253, 253, 253, 254, 254, 254, 254, 254, 254, 255, 255, 255, 255, 255, 255, 255, 256, 256, 256, 256, 256, 256, 256, 256, 256] : Array ℕ)[m]?.getD 0
  | 9 => if m = 158 then 306 else 0
  | _ => 0

def SplitInequality (d a b : ℕ) : Prop :=
  profile (d + 1) (a + b) ≤ max (profile d a) b + max (profile d b) a

instance (d a b : ℕ) : Decidable (SplitInequality d a b) := by
  unfold SplitInequality
  infer_instance

private theorem step0 (a : ℕ) (ha : a ≤ 1) :
    ∀ b : Fin 2, SplitInequality 0 a b := by
  interval_cases a <;> decide +kernel

private theorem step1 (a : ℕ) (ha : a ≤ 2) :
    ∀ b : Fin 3, SplitInequality 1 a b := by
  interval_cases a <;> decide +kernel

private theorem step2 (a : ℕ) (ha : a ≤ 4) :
    ∀ b : Fin 5, SplitInequality 2 a b := by
  interval_cases a <;> decide +kernel

private theorem step3 (a : ℕ) (ha : a ≤ 8) :
    ∀ b : Fin 9, SplitInequality 3 a b := by
  interval_cases a <;> decide +kernel

private theorem step4 (a : ℕ) (ha : a ≤ 16) :
    ∀ b : Fin 17, SplitInequality 4 a b := by
  interval_cases a <;> decide +kernel

private theorem step5 (a : ℕ) (ha : a ≤ 32) :
    ∀ b : Fin 33, SplitInequality 5 a b := by
  interval_cases a <;> decide +kernel

private theorem step6 (a : ℕ) (ha : a ≤ 64) :
    ∀ b : Fin 65, SplitInequality 6 a b := by
  interval_cases a <;> decide +kernel

private theorem step7 (a : ℕ) (ha : a ≤ 128) :
    ∀ b : Fin 129, SplitInequality 7 a b := by
  interval_cases a <;> decide +kernel

private theorem step8_at_158 (a : ℕ) (ha : a ≤ 158) :
    SplitInequality 8 a (158 - a) := by
  interval_cases a <;> decide +kernel

theorem profile_arithmetic (d : ℕ) (hd : d ≤ 8) (a b : ℕ)
    (ha : a ≤ 2 ^ d) (hb : b ≤ 2 ^ d) : SplitInequality d a b := by
  interval_cases d
  · exact step0 a ha ⟨b, by omega⟩
  · exact step1 a ha ⟨b, by omega⟩
  · exact step2 a ha ⟨b, by omega⟩
  · exact step3 a ha ⟨b, by omega⟩
  · exact step4 a ha ⟨b, by omega⟩
  · exact step5 a ha ⟨b, by omega⟩
  · exact step6 a ha ⟨b, by omega⟩
  · exact step7 a ha ⟨b, by omega⟩
  · by_cases h : a + b = 158
    · have hb' : b = 158 - a := by omega
      subst b
      exact step8_at_158 a (by omega)
    · change (if a + b = 158 then 306 else 0) ≤ _
      simp [h]

theorem near_refl (n : ℕ) (x : Cube n) : near n x x := by
  cases n with
  | zero => trivial
  | succ n =>
      change Cube n × Bool at x
      obtain ⟨x, b⟩ := x
      exact Or.inr rfl

theorem subset_closed (n : ℕ) (A : Finset (Cube n)) : A ⊆ closed n A := by
  intro x hx
  exact mem_closed.mpr ⟨x, hx, near_refl n x⟩

private theorem profile_zero (A : Finset (Cube 0)) :
    profile 0 A.card ≤ (closed 0 A).card := by
  have hA : A.card ≤ 1 := by
    have := Finset.card_le_univ A
    rw [cube_card] at this
    simpa using this
  have h := Finset.card_le_card (subset_closed 0 A)
  have hp : profile 0 A.card = A.card := by
    have ha : A.card = 0 ∨ A.card = 1 := by omega
    rcases ha with e | e <;> rw [e] <;> decide +kernel
  simpa [hp] using h

theorem profile_valid (d : ℕ) (hd : d ≤ 9) (A : Finset (Cube d)) :
    profile d A.card ≤ (closed d A).card := by
  induction d with
  | zero => exact profile_zero A
  | succ d ih =>
      apply profile_step d (profile d) (profile (d + 1))
      · exact ih (by omega)
      · exact profile_arithmetic d (by omega)

theorem cube9_closed_of_card158 (A : Finset (Cube 9)) (h : A.card = 158) :
    306 ≤ (closed 9 A).card := by
  have hp := profile_valid 9 (by decide) A
  simpa [h, profile] using hp

#print axioms cube9_closed_of_card158

end NineSeparatedSubsetSums

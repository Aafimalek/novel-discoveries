import FiniteCaseCoverage

namespace CertifiedG449Rotation
open G449FiniteCoverage

def encodeWord (g : Nat → Nat) : Nat :=
  ((List.range 7).map fun i => g i * 3^i).sum

theorem encodeWord_expand (g : Nat → Nat) :
    encodeWord g = g 0 + g 1*3 + g 2*9 + g 3*27 + g 4*81 + g 5*243 + g 6*729 := by
  simp [encodeWord,List.range_succ] <;> omega

theorem encodeWord_lt (g : Nat → Nat) (h : ∀ i < 7, g i < 3) : encodeWord g < 2187 := by
  rw [encodeWord_expand]
  have t0 := h 0 (by decide)
  have t1 := h 1 (by decide)
  have t2 := h 2 (by decide)
  have t3 := h 3 (by decide)
  have t4 := h 4 (by decide)
  have t5 := h 5 (by decide)
  have t6 := h 6 (by decide)
  omega

theorem encodeWord_decode (g : Nat → Nat) (h : ∀ i < 7, g i < 3) (i : Nat) (hi : i < 7) :
    label (encodeWord g) i = g i := by
  have t0 := h 0 (by decide)
  have t1 := h 1 (by decide)
  have t2 := h 2 (by decide)
  have t3 := h 3 (by decide)
  have t4 := h 4 (by decide)
  have t5 := h 5 (by decide)
  have t6 := h 6 (by decide)
  have z : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 := by omega
  rcases z with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [label, encodeWord_expand] <;> omega

theorem encodeWord_congr (g h : Nat → Nat) (E : ∀ i < 7, g i = h i) :
    encodeWord g = encodeWord h := by
  unfold encodeWord
  rw [List.map_congr_left (g := fun i => h i * 3^i) (fun i hi => by rw [E i (List.mem_range.mp hi)])]

#print axioms encodeWord_decode
end CertifiedG449Rotation

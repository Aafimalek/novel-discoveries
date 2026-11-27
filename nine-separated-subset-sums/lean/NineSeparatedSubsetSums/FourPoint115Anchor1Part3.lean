import Lean.Elab.Tactic.Omega
import NineSeparatedSubsetSums.FourPoint115Anchor1Part3Chunk0
import NineSeparatedSubsetSums.FourPoint115Anchor1Part3Chunk1
import NineSeparatedSubsetSums.FourPoint115Anchor1Part3Chunk2
import NineSeparatedSubsetSums.FourPoint115Anchor1Part3Chunk3

namespace NineSeparatedSubsetSums

theorem fourPoint115Anchor1Part3 :
    ∀ j : Fin 117, ((j.val : Int)+357+115)%2=1 →
      1036084 ≤ FourPointNumeric.charge 115 fourPoint115Table1
        ((j.val : Int)+357) := by
  intro j hp
  by_cases h0 : j.val < 30
  · let k : Fin 30 := ⟨j.val-0, by have := j.isLt; omega⟩
    have e : (k.val : Int)+357 = (j.val : Int)+357 := by dsimp [k] <;> omega
    have h := fourPoint115Anchor1Part3Chunk0 k
    rw [e] at h
    exact h hp
  by_cases h1 : j.val < 60
  · let k : Fin 30 := ⟨j.val-30, by have := j.isLt; omega⟩
    have e : (k.val : Int)+387 = (j.val : Int)+357 := by dsimp [k] <;> omega
    have h := fourPoint115Anchor1Part3Chunk1 k
    rw [e] at h
    exact h hp
  by_cases h2 : j.val < 90
  · let k : Fin 30 := ⟨j.val-60, by have := j.isLt; omega⟩
    have e : (k.val : Int)+417 = (j.val : Int)+357 := by dsimp [k] <;> omega
    have h := fourPoint115Anchor1Part3Chunk2 k
    rw [e] at h
    exact h hp
  let k : Fin 27 := ⟨j.val-90, by have := j.isLt; omega⟩
  have e : (k.val : Int)+447 = (j.val : Int)+357 := by dsimp [k] <;> omega
  have h := fourPoint115Anchor1Part3Chunk3 k
  rw [e] at h
  exact h hp

end NineSeparatedSubsetSums

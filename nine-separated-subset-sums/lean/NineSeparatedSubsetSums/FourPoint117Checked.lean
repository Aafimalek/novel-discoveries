import NineSeparatedSubsetSums.FourPointPackedGeometry
import NineSeparatedSubsetSums.FourPoint117PackedBudget0
import NineSeparatedSubsetSums.FourPoint117PackedAnchor0Part0
import NineSeparatedSubsetSums.FourPoint117PackedAnchor0Part1
import NineSeparatedSubsetSums.FourPoint117PackedBudget1
import NineSeparatedSubsetSums.FourPoint117PackedAnchor1Part0
import NineSeparatedSubsetSums.FourPoint117PackedAnchor1Part1
import NineSeparatedSubsetSums.FourPoint117PackedAnchor1Part2

namespace NineSeparatedSubsetSums

private theorem packed117Anchor0 :
  ∀ j : Fin 481, ((j.val : Int)+117)%2=0 →
    1064600 ≤ FourPointNumeric.packedCharge 117 20 packedWeight117_0 (j.val : Int) := by
  intro j hj
  let k := (j.val-1)/2
  have hk : k < 240 := by dsimp [k]; have h := j.isLt; omega
  have hrep : 2*(k : Int)+1 = j.val := by dsimp [k]; omega
  by_cases h0 : k < 120
  · let z : Fin 120 := ⟨k-0, by omega⟩
    have he : (z.val : Int)+0 = k := by dsimp [z] <;> omega
    have ht := fourPoint117PackedAnchor0Part0 z
    rwa [he,hrep] at ht
  let z : Fin 120 := ⟨k-120, by omega⟩
  have he : (z.val : Int)+120 = k := by dsimp [z] <;> omega
  have ht := fourPoint117PackedAnchor0Part1 z
  rwa [he,hrep] at ht

private theorem packed117Anchor1 :
  ∀ j : Fin 481, ((j.val : Int)+117)%2=1 →
    1064612 ≤ FourPointNumeric.packedCharge 117 20 packedWeight117_1 (j.val : Int) := by
  intro j hj
  let k := (j.val-0)/2
  have hk : k < 241 := by dsimp [k]; have h := j.isLt; omega
  have hrep : 2*(k : Int)+0 = j.val := by dsimp [k]; omega
  by_cases h0 : k < 120
  · let z : Fin 120 := ⟨k-0, by omega⟩
    have he : (z.val : Int)+0 = k := by dsimp [z] <;> omega
    have ht := fourPoint117PackedAnchor1Part0 z
    rwa [he,hrep] at ht
  by_cases h1 : k < 240
  · let z : Fin 120 := ⟨k-120, by omega⟩
    have he : (z.val : Int)+120 = k := by dsimp [z] <;> omega
    have ht := fourPoint117PackedAnchor1Part1 z
    rwa [he,hrep] at ht
  let z : Fin 1 := ⟨k-240, by omega⟩
  have he : (z.val : Int)+240 = k := by dsimp [z] <;> omega
  have ht := fourPoint117PackedAnchor1Part2 z
  rwa [he,hrep] at ht

def packedCertificate117_0 : FourPointCertificate 117 0 109179 :=
  fourPointCertificateOfPacked 117 0 109179 1064600 20 packedWeight117_0 571 481
    (by decide +kernel) (by decide) (by decide) packed117Anchor0
    (by rw [packedWeight117_0_budget]; decide)

def packedCertificate117_1 : FourPointCertificate 117 1 109179 :=
  fourPointCertificateOfPacked 117 1 109179 1064612 20 packedWeight117_1 566 481
    (by decide +kernel) (by decide) (by decide) packed117Anchor1
    (by rw [packedWeight117_1_budget]; decide)

theorem max148_second117_fourPoint_moment_bound (tail : List ℕ) (len : tail.length=7)
    (distinct : (natSubsetSums (148::117::tail)).Nodup) :
    109179 ≤ ((148::117::tail).map (· ^ 2)).sum := by
  apply fourPointNatMomentLower 117 109179 tail len distinct
  intro p hp
  by_cases h : p=0
  · subst p
    exact packedCertificate117_0
  · have he : p=1 := hp.resolve_left h
    subst p
    exact packedCertificate117_1

#print axioms max148_second117_fourPoint_moment_bound

end NineSeparatedSubsetSums

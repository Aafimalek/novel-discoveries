import NineSeparatedSubsetSums.FourPointPackedGeometry
import NineSeparatedSubsetSums.FourPoint116PackedBudget0
import NineSeparatedSubsetSums.FourPoint116PackedAnchor0Part0
import NineSeparatedSubsetSums.FourPoint116PackedAnchor0Part1
import NineSeparatedSubsetSums.FourPoint116PackedBudget1
import NineSeparatedSubsetSums.FourPoint116PackedAnchor1Part0
import NineSeparatedSubsetSums.FourPoint116PackedAnchor1Part1

namespace NineSeparatedSubsetSums

private theorem packed116Anchor0 :
  ∀ j : Fin 475, ((j.val : Int)+116)%2=0 →
    1043136 ≤ FourPointNumeric.packedCharge 116 20 packedWeight116_0 (j.val : Int) := by
  intro j hj
  let k := (j.val-0)/2
  have hk : k < 238 := by dsimp [k]; have h := j.isLt; omega
  have hrep : 2*(k : Int)+0 = j.val := by dsimp [k]; omega
  by_cases h0 : k < 120
  · let z : Fin 120 := ⟨k-0, by omega⟩
    have he : (z.val : Int)+0 = k := by dsimp [z] <;> omega
    have ht := fourPoint116PackedAnchor0Part0 z
    rwa [he,hrep] at ht
  let z : Fin 118 := ⟨k-120, by omega⟩
  have he : (z.val : Int)+120 = k := by dsimp [z] <;> omega
  have ht := fourPoint116PackedAnchor0Part1 z
  rwa [he,hrep] at ht

private theorem packed116Anchor1 :
  ∀ j : Fin 475, ((j.val : Int)+116)%2=1 →
    1043012 ≤ FourPointNumeric.packedCharge 116 20 packedWeight116_1 (j.val : Int) := by
  intro j hj
  let k := (j.val-1)/2
  have hk : k < 237 := by dsimp [k]; have h := j.isLt; omega
  have hrep : 2*(k : Int)+1 = j.val := by dsimp [k]; omega
  by_cases h0 : k < 120
  · let z : Fin 120 := ⟨k-0, by omega⟩
    have he : (z.val : Int)+0 = k := by dsimp [z] <;> omega
    have ht := fourPoint116PackedAnchor1Part0 z
    rwa [he,hrep] at ht
  let z : Fin 117 := ⟨k-120, by omega⟩
  have he : (z.val : Int)+120 = k := by dsimp [z] <;> omega
  have ht := fourPoint116PackedAnchor1Part1 z
  rwa [he,hrep] at ht

def packedCertificate116_0 : FourPointCertificate 116 0 109278 :=
  fourPointCertificateOfPacked 116 0 109278 1043136 20 packedWeight116_0 445 475
    (by decide +kernel) (by decide) (by decide) packed116Anchor0
    (by rw [packedWeight116_0_budget]; decide)

def packedCertificate116_1 : FourPointCertificate 116 1 109278 :=
  fourPointCertificateOfPacked 116 1 109278 1043012 20 packedWeight116_1 444 475
    (by decide +kernel) (by decide) (by decide) packed116Anchor1
    (by rw [packedWeight116_1_budget]; decide)

theorem max148_second116_fourPoint_moment_bound (tail : List ℕ) (len : tail.length=7)
    (distinct : (natSubsetSums (148::116::tail)).Nodup) :
    109278 ≤ ((148::116::tail).map (· ^ 2)).sum := by
  apply fourPointNatMomentLower 116 109278 tail len distinct
  intro p hp
  by_cases h : p=0
  · subst p
    exact packedCertificate116_0
  · have he : p=1 := hp.resolve_left h
    subst p
    exact packedCertificate116_1

#print axioms max148_second116_fourPoint_moment_bound

end NineSeparatedSubsetSums

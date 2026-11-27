import NineSeparatedSubsetSums.FourPointPackedGeometry
import NineSeparatedSubsetSums.FourPoint118PackedBudget0
import NineSeparatedSubsetSums.FourPoint118PackedAnchor0Part0
import NineSeparatedSubsetSums.FourPoint118PackedAnchor0Part1
import NineSeparatedSubsetSums.FourPoint118PackedAnchor0Part2
import NineSeparatedSubsetSums.FourPoint118PackedBudget1
import NineSeparatedSubsetSums.FourPoint118PackedAnchor1Part0
import NineSeparatedSubsetSums.FourPoint118PackedAnchor1Part1
import NineSeparatedSubsetSums.FourPoint118PackedAnchor1Part2

namespace NineSeparatedSubsetSums

private theorem packed118Anchor0 :
  ∀ j : Fin 484, ((j.val : Int)+118)%2=0 →
    1077792 ≤ FourPointNumeric.packedCharge 118 20 packedWeight118_0 (j.val : Int) := by
  intro j hj
  let k := (j.val-0)/2
  have hk : k < 242 := by dsimp [k]; have h := j.isLt; omega
  have hrep : 2*(k : Int)+0 = j.val := by dsimp [k]; omega
  by_cases h0 : k < 120
  · let z : Fin 120 := ⟨k-0, by omega⟩
    have he : (z.val : Int)+0 = k := by dsimp [z] <;> omega
    have ht := fourPoint118PackedAnchor0Part0 z
    rwa [he,hrep] at ht
  by_cases h1 : k < 240
  · let z : Fin 120 := ⟨k-120, by omega⟩
    have he : (z.val : Int)+120 = k := by dsimp [z] <;> omega
    have ht := fourPoint118PackedAnchor0Part1 z
    rwa [he,hrep] at ht
  let z : Fin 2 := ⟨k-240, by omega⟩
  have he : (z.val : Int)+240 = k := by dsimp [z] <;> omega
  have ht := fourPoint118PackedAnchor0Part2 z
  rwa [he,hrep] at ht

private theorem packed118Anchor1 :
  ∀ j : Fin 484, ((j.val : Int)+118)%2=1 →
    1077780 ≤ FourPointNumeric.packedCharge 118 20 packedWeight118_1 (j.val : Int) := by
  intro j hj
  let k := (j.val-1)/2
  have hk : k < 242 := by dsimp [k]; have h := j.isLt; omega
  have hrep : 2*(k : Int)+1 = j.val := by dsimp [k]; omega
  by_cases h0 : k < 120
  · let z : Fin 120 := ⟨k-0, by omega⟩
    have he : (z.val : Int)+0 = k := by dsimp [z] <;> omega
    have ht := fourPoint118PackedAnchor1Part0 z
    rwa [he,hrep] at ht
  by_cases h1 : k < 240
  · let z : Fin 120 := ⟨k-120, by omega⟩
    have he : (z.val : Int)+120 = k := by dsimp [z] <;> omega
    have ht := fourPoint118PackedAnchor1Part1 z
    rwa [he,hrep] at ht
  let z : Fin 2 := ⟨k-240, by omega⟩
  have he : (z.val : Int)+240 = k := by dsimp [z] <;> omega
  have ht := fourPoint118PackedAnchor1Part2 z
  rwa [he,hrep] at ht

def packedCertificate118_0 : FourPointCertificate 118 0 109014 :=
  fourPointCertificateOfPacked 118 0 109014 1077792 20 packedWeight118_0 471 484
    (by decide +kernel) (by decide) (by decide) packed118Anchor0
    (by rw [packedWeight118_0_budget]; decide)

def packedCertificate118_1 : FourPointCertificate 118 1 109014 :=
  fourPointCertificateOfPacked 118 1 109014 1077780 20 packedWeight118_1 544 484
    (by decide +kernel) (by decide) (by decide) packed118Anchor1
    (by rw [packedWeight118_1_budget]; decide)

theorem max148_second118_fourPoint_moment_bound (tail : List ℕ) (len : tail.length=7)
    (distinct : (natSubsetSums (148::118::tail)).Nodup) :
    109014 ≤ ((148::118::tail).map (· ^ 2)).sum := by
  apply fourPointNatMomentLower 118 109014 tail len distinct
  intro p hp
  by_cases h : p=0
  · subst p
    exact packedCertificate118_0
  · have he : p=1 := hp.resolve_left h
    subst p
    exact packedCertificate118_1

#print axioms max148_second118_fourPoint_moment_bound

end NineSeparatedSubsetSums

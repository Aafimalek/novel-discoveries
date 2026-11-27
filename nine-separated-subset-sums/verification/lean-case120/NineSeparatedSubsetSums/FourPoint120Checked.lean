import NineSeparatedSubsetSums.FourPointPackedGeometry
import NineSeparatedSubsetSums.FourPoint120PackedBudget0
import NineSeparatedSubsetSums.FourPoint120PackedAnchor0Part0
import NineSeparatedSubsetSums.FourPoint120PackedAnchor0Part1
import NineSeparatedSubsetSums.FourPoint120PackedBudget1
import NineSeparatedSubsetSums.FourPoint120PackedAnchor1Part0
import NineSeparatedSubsetSums.FourPoint120PackedAnchor1Part1

namespace NineSeparatedSubsetSums

private theorem packed120Anchor0 :
  ∀ j : Fin 469, ((j.val : Int)+120)%2=0 →
    1022592 ≤ FourPointNumeric.packedCharge 120 20 packedWeight120_0 (j.val : Int) := by
  intro j hj
  let k := (j.val-0)/2
  have hk : k < 235 := by dsimp [k]; have h := j.isLt; omega
  have hrep : 2*(k : Int)+0 = j.val := by dsimp [k]; omega
  by_cases h0 : k < 120
  · let z : Fin 120 := ⟨k-0, by omega⟩
    have he : (z.val : Int)+0 = k := by dsimp [z] <;> omega
    have ht := fourPoint120PackedAnchor0Part0 z
    rwa [he,hrep] at ht
  let z : Fin 115 := ⟨k-120, by omega⟩
  have he : (z.val : Int)+120 = k := by dsimp [z] <;> omega
  have ht := fourPoint120PackedAnchor0Part1 z
  rwa [he,hrep] at ht

private theorem packed120Anchor1 :
  ∀ j : Fin 469, ((j.val : Int)+120)%2=1 →
    1022564 ≤ FourPointNumeric.packedCharge 120 20 packedWeight120_1 (j.val : Int) := by
  intro j hj
  let k := (j.val-1)/2
  have hk : k < 234 := by dsimp [k]; have h := j.isLt; omega
  have hrep : 2*(k : Int)+1 = j.val := by dsimp [k]; omega
  by_cases h0 : k < 120
  · let z : Fin 120 := ⟨k-0, by omega⟩
    have he : (z.val : Int)+0 = k := by dsimp [z] <;> omega
    have ht := fourPoint120PackedAnchor1Part0 z
    rwa [he,hrep] at ht
  let z : Fin 114 := ⟨k-120, by omega⟩
  have he : (z.val : Int)+120 = k := by dsimp [z] <;> omega
  have ht := fourPoint120PackedAnchor1Part1 z
  rwa [he,hrep] at ht

def packedCertificate120_0 : FourPointCertificate 120 0 108497 :=
  fourPointCertificateOfPacked 120 0 108497 1022592 20 packedWeight120_0 469 469
    (by decide +kernel) (by decide) (by decide) packed120Anchor0
    (by rw [packedWeight120_0_budget]; decide)

def packedCertificate120_1 : FourPointCertificate 120 1 108497 :=
  fourPointCertificateOfPacked 120 1 108497 1022564 20 packedWeight120_1 576 469
    (by decide +kernel) (by decide) (by decide) packed120Anchor1
    (by rw [packedWeight120_1_budget]; decide)

theorem max148_second120_fourPoint_moment_bound (tail : List ℕ) (len : tail.length=7)
    (distinct : (natSubsetSums (148::120::tail)).Nodup) :
    108497 ≤ ((148::120::tail).map (· ^ 2)).sum := by
  apply fourPointNatMomentLower 120 108497 tail len distinct
  intro p hp
  by_cases h : p=0
  · subst p
    exact packedCertificate120_0
  · have he : p=1 := hp.resolve_left h
    subst p
    exact packedCertificate120_1

#print axioms max148_second120_fourPoint_moment_bound

end NineSeparatedSubsetSums

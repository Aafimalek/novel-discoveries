import NineSeparatedSubsetSums.EightPointPackedGeometry
import NineSeparatedSubsetSums.EightPoint120_119PackedBudget0
import NineSeparatedSubsetSums.EightPoint120_119PackedAnchor0Part0
import NineSeparatedSubsetSums.EightPoint120_119PackedAnchor0Part1
import NineSeparatedSubsetSums.EightPoint120_119PackedBudget1
import NineSeparatedSubsetSums.EightPoint120_119PackedAnchor1Part0
import NineSeparatedSubsetSums.EightPoint120_119PackedAnchor1Part1

namespace NineSeparatedSubsetSums

private theorem packedOct120_119Anchor0 :
  ∀ j : Fin 472, ((j.val : Int)+120+119)%2=0 →
    2181420 ≤ FourPointNumeric.octPackedCharge 120 119 20 packedOct120_119_0 (j.val : Int) := by
  intro j hj
  let k := (j.val-1)/2
  have hk : k < 236 := by dsimp [k]; have h := j.isLt; omega
  have hrep : 2*(k : Int)+1 = j.val := by dsimp [k]; omega
  by_cases h0 : k < 120
  · let z : Fin 120 := ⟨k-0, by omega⟩
    have he : (z.val : Int)+0 = k := by dsimp [z] <;> omega
    have ht := eightPoint120_119PackedAnchor0Part0 z
    rwa [he,hrep] at ht
  let z : Fin 116 := ⟨k-120, by omega⟩
  have he : (z.val : Int)+120 = k := by dsimp [z] <;> omega
  have ht := eightPoint120_119PackedAnchor0Part1 z
  rwa [he,hrep] at ht

private theorem packedOct120_119Anchor1 :
  ∀ j : Fin 472, ((j.val : Int)+120+119)%2=1 →
    2182547 ≤ FourPointNumeric.octPackedCharge 120 119 20 packedOct120_119_1 (j.val : Int) := by
  intro j hj
  let k := (j.val-0)/2
  have hk : k < 236 := by dsimp [k]; have h := j.isLt; omega
  have hrep : 2*(k : Int)+0 = j.val := by dsimp [k]; omega
  by_cases h0 : k < 120
  · let z : Fin 120 := ⟨k-0, by omega⟩
    have he : (z.val : Int)+0 = k := by dsimp [z] <;> omega
    have ht := eightPoint120_119PackedAnchor1Part0 z
    rwa [he,hrep] at ht
  let z : Fin 116 := ⟨k-120, by omega⟩
  have he : (z.val : Int)+120 = k := by dsimp [z] <;> omega
  have ht := eightPoint120_119PackedAnchor1Part1 z
  rwa [he,hrep] at ht

def packedOctCertificate120_119_0 : EightPointCertificate 120 119 0 121795 :=
  eightPointCertificateOfPacked 120 119 0 121795 2181420 20 packedOct120_119_0 495 472
    (by decide +kernel) (by decide) packedOct120_119Anchor0
    (by rw [packedOct120_119_0_budget]; decide)

def packedOctCertificate120_119_1 : EightPointCertificate 120 119 1 121795 :=
  eightPointCertificateOfPacked 120 119 1 121795 2182547 20 packedOct120_119_1 490 472
    (by decide +kernel) (by decide) packedOct120_119Anchor1
    (by rw [packedOct120_119_1_budget]; decide)

theorem max148_second120_third119_eightPoint_moment_bound (tail : List ℕ) (len : tail.length=6)
    (distinct : (natSubsetSums (148::120::119::tail)).Nodup) :
    121795 ≤ ((148::120::119::tail).map (· ^ 2)).sum := by
  apply eightPointNatMomentLower 120 119 121795 tail len distinct
  intro p hp
  by_cases h : p=0
  · subst p
    exact packedOctCertificate120_119_0
  · have he : p=1 := hp.resolve_left h
    subst p
    exact packedOctCertificate120_119_1

#print axioms max148_second120_third119_eightPoint_moment_bound

end NineSeparatedSubsetSums

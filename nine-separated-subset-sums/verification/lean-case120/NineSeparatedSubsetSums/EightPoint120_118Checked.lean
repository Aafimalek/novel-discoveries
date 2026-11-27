import NineSeparatedSubsetSums.EightPointPackedGeometry
import NineSeparatedSubsetSums.EightPoint120_118PackedBudget0
import NineSeparatedSubsetSums.EightPoint120_118PackedAnchor0Part0
import NineSeparatedSubsetSums.EightPoint120_118PackedAnchor0Part1
import NineSeparatedSubsetSums.EightPoint120_118PackedBudget1
import NineSeparatedSubsetSums.EightPoint120_118PackedAnchor1Part0
import NineSeparatedSubsetSums.EightPoint120_118PackedAnchor1Part1

namespace NineSeparatedSubsetSums

private theorem packedOct120_118Anchor0 :
  ∀ j : Fin 471, ((j.val : Int)+120+118)%2=0 →
    2176236 ≤ FourPointNumeric.octPackedCharge 120 118 20 packedOct120_118_0 (j.val : Int) := by
  intro j hj
  let k := (j.val-0)/2
  have hk : k < 236 := by dsimp [k]; have h := j.isLt; omega
  have hrep : 2*(k : Int)+0 = j.val := by dsimp [k]; omega
  by_cases h0 : k < 120
  · let z : Fin 120 := ⟨k-0, by omega⟩
    have he : (z.val : Int)+0 = k := by dsimp [z] <;> omega
    have ht := eightPoint120_118PackedAnchor0Part0 z
    rwa [he,hrep] at ht
  let z : Fin 116 := ⟨k-120, by omega⟩
  have he : (z.val : Int)+120 = k := by dsimp [z] <;> omega
  have ht := eightPoint120_118PackedAnchor0Part1 z
  rwa [he,hrep] at ht

private theorem packedOct120_118Anchor1 :
  ∀ j : Fin 471, ((j.val : Int)+120+118)%2=1 →
    2175060 ≤ FourPointNumeric.octPackedCharge 120 118 20 packedOct120_118_1 (j.val : Int) := by
  intro j hj
  let k := (j.val-1)/2
  have hk : k < 235 := by dsimp [k]; have h := j.isLt; omega
  have hrep : 2*(k : Int)+1 = j.val := by dsimp [k]; omega
  by_cases h0 : k < 120
  · let z : Fin 120 := ⟨k-0, by omega⟩
    have he : (z.val : Int)+0 = k := by dsimp [z] <;> omega
    have ht := eightPoint120_118PackedAnchor1Part0 z
    rwa [he,hrep] at ht
  let z : Fin 115 := ⟨k-120, by omega⟩
  have he : (z.val : Int)+120 = k := by dsimp [z] <;> omega
  have ht := eightPoint120_118PackedAnchor1Part1 z
  rwa [he,hrep] at ht

def packedOctCertificate120_118_0 : EightPointCertificate 120 118 0 121680 :=
  eightPointCertificateOfPacked 120 118 0 121680 2176236 20 packedOct120_118_0 407 471
    (by decide +kernel) (by decide) packedOct120_118Anchor0
    (by rw [packedOct120_118_0_budget]; decide)

def packedOctCertificate120_118_1 : EightPointCertificate 120 118 1 121680 :=
  eightPointCertificateOfPacked 120 118 1 121680 2175060 20 packedOct120_118_1 500 471
    (by decide +kernel) (by decide) packedOct120_118Anchor1
    (by rw [packedOct120_118_1_budget]; decide)

theorem max148_second120_third118_eightPoint_moment_bound (tail : List ℕ) (len : tail.length=6)
    (distinct : (natSubsetSums (148::120::118::tail)).Nodup) :
    121680 ≤ ((148::120::118::tail).map (· ^ 2)).sum := by
  apply eightPointNatMomentLower 120 118 121680 tail len distinct
  intro p hp
  by_cases h : p=0
  · subst p
    exact packedOctCertificate120_118_0
  · have he : p=1 := hp.resolve_left h
    subst p
    exact packedOctCertificate120_118_1

#print axioms max148_second120_third118_eightPoint_moment_bound

end NineSeparatedSubsetSums

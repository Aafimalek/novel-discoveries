import NineSeparatedSubsetSums.FourPointPackedGeometry
import NineSeparatedSubsetSums.FourPoint119PackedBudget0
import NineSeparatedSubsetSums.FourPoint119PackedAnchor0Part0
import NineSeparatedSubsetSums.FourPoint119PackedAnchor0Part1
import NineSeparatedSubsetSums.FourPoint119PackedAnchor0Part2
import NineSeparatedSubsetSums.FourPoint119PackedBudget1
import NineSeparatedSubsetSums.FourPoint119PackedAnchor1Part0
import NineSeparatedSubsetSums.FourPoint119PackedAnchor1Part1
import NineSeparatedSubsetSums.FourPoint119PackedAnchor1Part2

namespace NineSeparatedSubsetSums

private theorem packed119Anchor0 :
  ∀ j : Fin 487, ((j.val : Int)+119)%2=0 →
    1090968 ≤ FourPointNumeric.packedCharge 119 20 packedWeight119_0 (j.val : Int) := by
  intro j hj
  let k := (j.val-1)/2
  have hk : k < 243 := by dsimp [k]; have h := j.isLt; omega
  have hrep : 2*(k : Int)+1 = j.val := by dsimp [k]; omega
  by_cases h0 : k < 120
  · let z : Fin 120 := ⟨k-0, by omega⟩
    have he : (z.val : Int)+0 = k := by dsimp [z] <;> omega
    have ht := fourPoint119PackedAnchor0Part0 z
    rwa [he,hrep] at ht
  by_cases h1 : k < 240
  · let z : Fin 120 := ⟨k-120, by omega⟩
    have he : (z.val : Int)+120 = k := by dsimp [z] <;> omega
    have ht := fourPoint119PackedAnchor0Part1 z
    rwa [he,hrep] at ht
  let z : Fin 3 := ⟨k-240, by omega⟩
  have he : (z.val : Int)+240 = k := by dsimp [z] <;> omega
  have ht := fourPoint119PackedAnchor0Part2 z
  rwa [he,hrep] at ht

private theorem packed119Anchor1 :
  ∀ j : Fin 487, ((j.val : Int)+119)%2=1 →
    1090948 ≤ FourPointNumeric.packedCharge 119 20 packedWeight119_1 (j.val : Int) := by
  intro j hj
  let k := (j.val-0)/2
  have hk : k < 244 := by dsimp [k]; have h := j.isLt; omega
  have hrep : 2*(k : Int)+0 = j.val := by dsimp [k]; omega
  by_cases h0 : k < 120
  · let z : Fin 120 := ⟨k-0, by omega⟩
    have he : (z.val : Int)+0 = k := by dsimp [z] <;> omega
    have ht := fourPoint119PackedAnchor1Part0 z
    rwa [he,hrep] at ht
  by_cases h1 : k < 240
  · let z : Fin 120 := ⟨k-120, by omega⟩
    have he : (z.val : Int)+120 = k := by dsimp [z] <;> omega
    have ht := fourPoint119PackedAnchor1Part1 z
    rwa [he,hrep] at ht
  let z : Fin 4 := ⟨k-240, by omega⟩
  have he : (z.val : Int)+240 = k := by dsimp [z] <;> omega
  have ht := fourPoint119PackedAnchor1Part2 z
  rwa [he,hrep] at ht

def packedCertificate119_0 : FourPointCertificate 119 0 108780 :=
  fourPointCertificateOfPacked 119 0 108780 1090968 20 packedWeight119_0 461 487
    (by decide +kernel) (by decide) (by decide) packed119Anchor0
    (by rw [packedWeight119_0_budget]; decide)

def packedCertificate119_1 : FourPointCertificate 119 1 108780 :=
  fourPointCertificateOfPacked 119 1 108780 1090948 20 packedWeight119_1 466 487
    (by decide +kernel) (by decide) (by decide) packed119Anchor1
    (by rw [packedWeight119_1_budget]; decide)

theorem max148_second119_fourPoint_moment_bound (tail : List ℕ) (len : tail.length=7)
    (distinct : (natSubsetSums (148::119::tail)).Nodup) :
    108780 ≤ ((148::119::tail).map (· ^ 2)).sum := by
  apply fourPointNatMomentLower 119 108780 tail len distinct
  intro p hp
  by_cases h : p=0
  · subst p
    exact packedCertificate119_0
  · have he : p=1 := hp.resolve_left h
    subst p
    exact packedCertificate119_1

#print axioms max148_second119_fourPoint_moment_bound

end NineSeparatedSubsetSums

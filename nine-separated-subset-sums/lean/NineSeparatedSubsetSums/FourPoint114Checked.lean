import NineSeparatedSubsetSums.FourPoint114Anchor0Part0
import NineSeparatedSubsetSums.FourPoint114Anchor0Part1
import NineSeparatedSubsetSums.FourPoint114Anchor0Part2
import NineSeparatedSubsetSums.FourPoint114Anchor0Part3
import NineSeparatedSubsetSums.FourPoint114Budget0
import NineSeparatedSubsetSums.FourPoint114Anchor1Part0
import NineSeparatedSubsetSums.FourPoint114Anchor1Part1
import NineSeparatedSubsetSums.FourPoint114Anchor1Part2
import NineSeparatedSubsetSums.FourPoint114Anchor1Part3
import NineSeparatedSubsetSums.FourPoint114Budget1

open scoped BigOperators
namespace NineSeparatedSubsetSums

theorem fourPoint114PositiveAnchor0 :
    ∀ j : Fin 472, ((j.val : ℤ)+114)%2=0 →
      1028128 ≤ blockCharge 114 (fun z => z^2+fourPointLookupPenalty fourPoint114Table0 z)
        (j.val : ℤ) := by
  intro j hp
  by_cases h₀ : j.val < 118
  · let k : Fin 118 := ⟨j.val, h₀⟩
    simpa [k] using fourPoint114Anchor0Part0 k (by simpa [k] using hp)
  by_cases h₁ : j.val < 236
  · let k : Fin 118 := ⟨j.val-118, by omega⟩
    have E : (k.val : ℤ)+118 = j.val := by dsimp [k]; omega
    have eq := fourPoint114Anchor0Part1 k
    rw [E] at eq
    exact eq hp
  by_cases h₂ : j.val < 354
  · let k : Fin 118 := ⟨j.val-236, by omega⟩
    have E : (k.val : ℤ)+236 = j.val := by dsimp [k]; omega
    have eq := fourPoint114Anchor0Part2 k
    rw [E] at eq
    exact eq hp
  · have hj := j.isLt
    let k : Fin 118 := ⟨j.val-354, by omega⟩
    have E : (k.val : ℤ)+354 = j.val := by dsimp [k]; omega
    have eq := fourPoint114Anchor0Part3 k
    rw [E] at eq
    exact eq hp

def fourPoint114Certificate0 : FourPointCertificate 114 0 109216 :=
  fourPointCertificateOfTable 114 0 109216 1028128 fourPoint114Table0 (by decide)
    (fun j hj => blockCharge_check_from_positive_window 114 1028128 0
      (fourPointLookupPenalty fourPoint114Table0) (fun _ => Int.natCast_nonneg _)
      (fourPointLookupPenalty_neg fourPoint114Table0) 472 (by decide)
      fourPoint114PositiveAnchor0 ((j.val : ℤ)-800) hj)
    (by rw [fourPoint114Budget0]; decide)

theorem fourPoint114PositiveAnchor1 :
    ∀ j : Fin 472, ((j.val : ℤ)+114)%2=1 →
      1027988 ≤ blockCharge 114 (fun z => z^2+fourPointLookupPenalty fourPoint114Table1 z)
        (j.val : ℤ) := by
  intro j hp
  by_cases h₀ : j.val < 118
  · let k : Fin 118 := ⟨j.val, h₀⟩
    simpa [k] using fourPoint114Anchor1Part0 k (by simpa [k] using hp)
  by_cases h₁ : j.val < 236
  · let k : Fin 118 := ⟨j.val-118, by omega⟩
    have E : (k.val : ℤ)+118 = j.val := by dsimp [k]; omega
    have eq := fourPoint114Anchor1Part1 k
    rw [E] at eq
    exact eq hp
  by_cases h₂ : j.val < 354
  · let k : Fin 118 := ⟨j.val-236, by omega⟩
    have E : (k.val : ℤ)+236 = j.val := by dsimp [k]; omega
    have eq := fourPoint114Anchor1Part2 k
    rw [E] at eq
    exact eq hp
  · have hj := j.isLt
    let k : Fin 118 := ⟨j.val-354, by omega⟩
    have E : (k.val : ℤ)+354 = j.val := by dsimp [k]; omega
    have eq := fourPoint114Anchor1Part3 k
    rw [E] at eq
    exact eq hp

def fourPoint114Certificate1 : FourPointCertificate 114 1 109216 :=
  fourPointCertificateOfTable 114 1 109216 1027988 fourPoint114Table1 (by decide)
    (fun j hj => blockCharge_check_from_positive_window 114 1027988 1
      (fourPointLookupPenalty fourPoint114Table1) (fun _ => Int.natCast_nonneg _)
      (fourPointLookupPenalty_neg fourPoint114Table1) 472 (by decide)
      fourPoint114PositiveAnchor1 ((j.val : ℤ)-800) hj)
    (by rw [fourPoint114Budget1]; decide)

/-- Both exact parity certificates imply this fixed strong cutoff. -/
theorem max148_second114_fourPoint_moment_bound (tail : List ℕ) (len : tail.length=7)
    (distinct : (natSubsetSums (148::114::tail)).Nodup) :
    109216 ≤ ((148::114::tail).map (· ^ 2)).sum := by
  apply fourPointNatMomentLower 114 109216 tail len distinct
  intro p hp
  by_cases h : p=0
  · subst p
    exact fourPoint114Certificate0
  · have he : p=1 := hp.resolve_left h
    subst p
    exact fourPoint114Certificate1

#print axioms max148_second114_fourPoint_moment_bound

end NineSeparatedSubsetSums

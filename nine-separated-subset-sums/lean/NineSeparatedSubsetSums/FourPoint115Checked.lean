import NineSeparatedSubsetSums.FourPointBudget
import NineSeparatedSubsetSums.FourPoint115Anchor0Part0
import NineSeparatedSubsetSums.FourPoint115Anchor0Part1
import NineSeparatedSubsetSums.FourPoint115Anchor0Part2
import NineSeparatedSubsetSums.FourPoint115Anchor0Part3
import NineSeparatedSubsetSums.FourPoint115Budget0
import NineSeparatedSubsetSums.FourPoint115Anchor1Part0
import NineSeparatedSubsetSums.FourPoint115Anchor1Part1
import NineSeparatedSubsetSums.FourPoint115Anchor1Part2
import NineSeparatedSubsetSums.FourPoint115Anchor1Part3
import NineSeparatedSubsetSums.FourPoint115Budget1

open scoped BigOperators
namespace NineSeparatedSubsetSums

theorem fourPoint115PositiveAnchor0 :
    ∀ j : Fin 474, ((j.val : ℤ)+115)%2=0 →
      1036088 ≤ blockCharge 115 (fun z => z^2+fourPointLookupPenalty fourPoint115Table0 z)
        (j.val : ℤ) := by
  intro j hp
  by_cases h₀ : j.val < 119
  · let k : Fin 119 := ⟨j.val, h₀⟩
    have E : (k.val : ℤ)+0 = j.val := by simp [k]
    have eq := fourPoint115Anchor0Part0 k
    rw [E] at eq
    exact eq hp
  by_cases h₁ : j.val < 238
  · let k : Fin 119 := ⟨j.val-119, by omega⟩
    have E : (k.val : ℤ)+119 = j.val := by dsimp [k]; omega
    have eq := fourPoint115Anchor0Part1 k
    rw [E] at eq
    exact eq hp
  by_cases h₂ : j.val < 357
  · let k : Fin 119 := ⟨j.val-238, by omega⟩
    have E : (k.val : ℤ)+238 = j.val := by dsimp [k]; omega
    have eq := fourPoint115Anchor0Part2 k
    rw [E] at eq
    exact eq hp
  · have hj := j.isLt
    let k : Fin 117 := ⟨j.val-357, by omega⟩
    have E : (k.val : ℤ)+357 = j.val := by dsimp [k]; omega
    have eq := fourPoint115Anchor0Part3 k
    rw [E] at eq
    exact eq hp

def fourPoint115Certificate0 : FourPointCertificate 115 0 109254 :=
  fourPointCertificateOfTable 115 0 109254 1036088 fourPoint115Table0 (by decide)
    (fun j hj => blockCharge_check_from_positive_window 115 1036088 0
      (fourPointLookupPenalty fourPoint115Table0) (fun _ => Int.natCast_nonneg _)
      (fourPointLookupPenalty_neg fourPoint115Table0) 474 (by decide)
      fourPoint115PositiveAnchor0 ((j.val : ℤ)-800) hj)
    (by
      rw [fourPointLookupBudget_eq]
      change 512 * (_ - 1) < 128 * _ - FourPointNumeric.budget fourPoint115Table0
      rw [fourPoint115Budget0]
      decide)

theorem fourPoint115PositiveAnchor1 :
    ∀ j : Fin 474, ((j.val : ℤ)+115)%2=1 →
      1036084 ≤ blockCharge 115 (fun z => z^2+fourPointLookupPenalty fourPoint115Table1 z)
        (j.val : ℤ) := by
  intro j hp
  by_cases h₀ : j.val < 119
  · let k : Fin 119 := ⟨j.val, h₀⟩
    have E : (k.val : ℤ)+0 = j.val := by simp [k]
    have eq := fourPoint115Anchor1Part0 k
    rw [E] at eq
    exact eq hp
  by_cases h₁ : j.val < 238
  · let k : Fin 119 := ⟨j.val-119, by omega⟩
    have E : (k.val : ℤ)+119 = j.val := by dsimp [k]; omega
    have eq := fourPoint115Anchor1Part1 k
    rw [E] at eq
    exact eq hp
  by_cases h₂ : j.val < 357
  · let k : Fin 119 := ⟨j.val-238, by omega⟩
    have E : (k.val : ℤ)+238 = j.val := by dsimp [k]; omega
    have eq := fourPoint115Anchor1Part2 k
    rw [E] at eq
    exact eq hp
  · have hj := j.isLt
    let k : Fin 117 := ⟨j.val-357, by omega⟩
    have E : (k.val : ℤ)+357 = j.val := by dsimp [k]; omega
    have eq := fourPoint115Anchor1Part3 k
    rw [E] at eq
    exact eq hp

def fourPoint115Certificate1 : FourPointCertificate 115 1 109254 :=
  fourPointCertificateOfTable 115 1 109254 1036084 fourPoint115Table1 (by decide)
    (fun j hj => blockCharge_check_from_positive_window 115 1036084 1
      (fourPointLookupPenalty fourPoint115Table1) (fun _ => Int.natCast_nonneg _)
      (fourPointLookupPenalty_neg fourPoint115Table1) 474 (by decide)
      fourPoint115PositiveAnchor1 ((j.val : ℤ)-800) hj)
    (by
      rw [fourPointLookupBudget_eq]
      change 512 * (_ - 1) < 128 * _ - FourPointNumeric.budget fourPoint115Table1
      rw [fourPoint115Budget1]
      decide)

/-- Both exact parity certificates imply this fixed strong cutoff. -/
theorem max148_second115_fourPoint_moment_bound (tail : List ℕ) (len : tail.length=7)
    (distinct : (natSubsetSums (148::115::tail)).Nodup) :
    109254 ≤ ((148::115::tail).map (· ^ 2)).sum := by
  apply fourPointNatMomentLower 115 109254 tail len distinct
  intro p hp
  by_cases h : p=0
  · subst p
    exact fourPoint115Certificate0
  · have he : p=1 := hp.resolve_left h
    subst p
    exact fourPoint115Certificate1

#print axioms max148_second115_fourPoint_moment_bound

end NineSeparatedSubsetSums

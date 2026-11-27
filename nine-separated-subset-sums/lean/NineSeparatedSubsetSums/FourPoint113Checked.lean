import NineSeparatedSubsetSums.FourPoint113Anchor0Part0
import NineSeparatedSubsetSums.FourPoint113Anchor0Part1
import NineSeparatedSubsetSums.FourPoint113Anchor0Part2
import NineSeparatedSubsetSums.FourPoint113Anchor0Part3
import NineSeparatedSubsetSums.FourPoint113Budget0
import NineSeparatedSubsetSums.FourPoint113Anchor1Part0
import NineSeparatedSubsetSums.FourPoint113Anchor1Part1
import NineSeparatedSubsetSums.FourPoint113Anchor1Part2
import NineSeparatedSubsetSums.FourPoint113Anchor1Part3
import NineSeparatedSubsetSums.FourPoint113Budget1

open scoped BigOperators
namespace NineSeparatedSubsetSums

theorem fourPoint113PositiveAnchor0 :
    ∀ j : Fin 469, ((j.val : ℤ)+113)%2=0 →
      1016472 ≤ blockCharge 113 (fun z => z^2+fourPointLookupPenalty fourPoint113Table0 z)
        (j.val : ℤ) := by
  intro j hp
  by_cases h₀ : j.val < 117
  · let k : Fin 117 := ⟨j.val, h₀⟩
    simpa [k] using fourPoint113Anchor0Part0 k (by simpa [k] using hp)
  by_cases h₁ : j.val < 234
  · let k : Fin 117 := ⟨j.val-117, by omega⟩
    have E : (k.val : ℤ)+117 = j.val := by dsimp [k]; omega
    have eq := fourPoint113Anchor0Part1 k
    rw [E] at eq
    exact eq hp
  by_cases h₂ : j.val < 351
  · let k : Fin 117 := ⟨j.val-234, by omega⟩
    have E : (k.val : ℤ)+234 = j.val := by dsimp [k]; omega
    have eq := fourPoint113Anchor0Part2 k
    rw [E] at eq
    exact eq hp
  · have hj := j.isLt
    let k : Fin 118 := ⟨j.val-351, by omega⟩
    have E : (k.val : ℤ)+351 = j.val := by dsimp [k]; omega
    have eq := fourPoint113Anchor0Part3 k
    rw [E] at eq
    exact eq hp

def fourPoint113Certificate0 : FourPointCertificate 113 0 109140 :=
  fourPointCertificateOfTable 113 0 109140 1016472 fourPoint113Table0 (by decide)
    (fun j hj => blockCharge_check_from_positive_window 113 1016472 0
      (fourPointLookupPenalty fourPoint113Table0) (fun _ => Int.natCast_nonneg _)
      (fourPointLookupPenalty_neg fourPoint113Table0) 469 (by decide)
      fourPoint113PositiveAnchor0 ((j.val : ℤ)-800) hj)
    (by rw [fourPoint113Budget0]; decide)

theorem fourPoint113PositiveAnchor1 :
    ∀ j : Fin 469, ((j.val : ℤ)+113)%2=1 →
      1016308 ≤ blockCharge 113 (fun z => z^2+fourPointLookupPenalty fourPoint113Table1 z)
        (j.val : ℤ) := by
  intro j hp
  by_cases h₀ : j.val < 117
  · let k : Fin 117 := ⟨j.val, h₀⟩
    simpa [k] using fourPoint113Anchor1Part0 k (by simpa [k] using hp)
  by_cases h₁ : j.val < 234
  · let k : Fin 117 := ⟨j.val-117, by omega⟩
    have E : (k.val : ℤ)+117 = j.val := by dsimp [k]; omega
    have eq := fourPoint113Anchor1Part1 k
    rw [E] at eq
    exact eq hp
  by_cases h₂ : j.val < 351
  · let k : Fin 117 := ⟨j.val-234, by omega⟩
    have E : (k.val : ℤ)+234 = j.val := by dsimp [k]; omega
    have eq := fourPoint113Anchor1Part2 k
    rw [E] at eq
    exact eq hp
  · have hj := j.isLt
    let k : Fin 118 := ⟨j.val-351, by omega⟩
    have E : (k.val : ℤ)+351 = j.val := by dsimp [k]; omega
    have eq := fourPoint113Anchor1Part3 k
    rw [E] at eq
    exact eq hp

def fourPoint113Certificate1 : FourPointCertificate 113 1 109140 :=
  fourPointCertificateOfTable 113 1 109140 1016308 fourPoint113Table1 (by decide)
    (fun j hj => blockCharge_check_from_positive_window 113 1016308 1
      (fourPointLookupPenalty fourPoint113Table1) (fun _ => Int.natCast_nonneg _)
      (fourPointLookupPenalty_neg fourPoint113Table1) 469 (by decide)
      fourPoint113PositiveAnchor1 ((j.val : ℤ)-800) hj)
    (by rw [fourPoint113Budget1]; decide)

/-- Both exact parity certificates imply this fixed strong cutoff. -/
theorem max148_second113_fourPoint_moment_bound (tail : List ℕ) (len : tail.length=7)
    (distinct : (natSubsetSums (148::113::tail)).Nodup) :
    109140 ≤ ((148::113::tail).map (· ^ 2)).sum := by
  apply fourPointNatMomentLower 113 109140 tail len distinct
  intro p hp
  by_cases h : p=0
  · subst p
    exact fourPoint113Certificate0
  · have he : p=1 := hp.resolve_left h
    subst p
    exact fourPoint113Certificate1

#print axioms max148_second113_fourPoint_moment_bound

end NineSeparatedSubsetSums

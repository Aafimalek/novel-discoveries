import Mod7Trace

namespace CyclotomicModSeven

def residue (a : Int) : F7 :=
  ⟨(a%7).toNat, by
    have h := Int.emod_lt_of_pos a (show (0:Int) < 7 by decide)
    omega⟩

theorem residue_val (a : Int) : ((residue a).val : Int) = a%7 := by
  change ((a%7).toNat : Int) = a%7
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))

theorem residue_add (a b : Int) : residue (a+b) = residue a+residue b := by
  apply Fin.ext
  apply Int.ofNat_inj.mp
  rw [residue_val, Fin.val_add, Int.natCast_emod, Int.natCast_add, residue_val, residue_val]
  exact Int.add_emod _ _ _

theorem residue_mul (a b : Int) : residue (a*b) = residue a*residue b := by
  apply Fin.ext
  apply Int.ofNat_inj.mp
  rw [residue_val, Fin.val_mul, Int.natCast_emod, Int.natCast_mul, residue_val, residue_val]
  exact Int.mul_emod _ _ _

private theorem sub_characterization : ∀ a b c : F7, c+b=a → c=a-b := by decide +kernel

theorem residue_sub (a b : Int) : residue (a-b) = residue a-residue b := by
  apply sub_characterization
  rw [← residue_add]
  have h : (a-b)+b=a := by omega
  rw [h]

@[simp] theorem residue_zero : residue 0 = 0 := by decide +kernel

theorem residue_nonzero_of_prime_to_seven (d : Int) (h : d%7 ≠ 0) :
    residue d ≠ 0 := by
  intro hd
  have t := residue_val d
  rw [hd] at t
  exact h t.symm

def inverse (a : F7) : F7 :=
  match a.val with
  | 1 => 1
  | 2 => 4
  | 3 => 5
  | 4 => 2
  | 5 => 3
  | 6 => 6
  | _ => 0

theorem normalized_pair_norm : ∀ a b d : F7, d ≠ 0 → a*b=d*d →
    (a*inverse d)*(b*inverse d)=1 := by decide +kernel

theorem normalized_sub : ∀ a b d e : F7, d ≠ 0 → e ≠ 0 →
    a*inverse d-b*inverse e=(e*a-d*b)*inverse (d*e) := by decide +kernel

theorem add_sub_pair : ∀ a b c d : F7, (a+b)-(c+d)=(a-c)+(b-d) := by decide +kernel

theorem nonzero_mul : ∀ a b : F7, a ≠ 0 → b ≠ 0 → a*b ≠ 0 := by decide +kernel

#print axioms residue_add
#print axioms residue_mul
#print axioms residue_sub
#print axioms normalized_pair_norm
#print axioms normalized_sub

end CyclotomicModSeven

/- Optional uncompiled draft: explicit finite Stieltjes decomposition. -/
import JointCapDraft

namespace WidthThree.JointPool

/-- Counting prefix, with zeros after the end of the supplied bins. -/
def prefixCount : Nat → List Nat → Nat
  | 0, _ => 0
  | _ + 1, [] => 0
  | k + 1, b :: bs => b + prefixCount k bs

def binsAntitone : List Nat → Prop
  | [] => True
  | b :: bs => bs.headD 0 ≤ b ∧ binsAntitone bs

def shift (layers : List (Nat × Nat)) : List (Nat × Nat) :=
  layers.map fun p => (p.1 + 1, p.2)

def mass : List (Nat × Nat) → Nat
  | [] => 0
  | p :: ps => p.2 + mass ps

def layersOf : List Nat → List (Nat × Nat)
  | [] => []
  | b :: bs => (1, b - bs.headD 0) :: shift (layersOf bs)

private theorem mass_shift (ls : List (Nat × Nat)) : mass (shift ls) = mass ls := by
  induction ls with
  | nil => rfl
  | cons p ps ih =>
    change p.2 + mass (shift ps) = p.2 + mass ps
    rw [ih]

private theorem cappedSum_zero (ls : List (Nat × Nat)) : cappedSum 0 ls = 0 := by
  induction ls with
  | nil => rfl
  | cons p ps ih =>
    rcases p with ⟨H,w⟩
    simp only [cappedSum, Nat.zero_min, Nat.mul_zero, ih, Nat.zero_add]

private theorem cappedSum_shift (k : Nat) (ls : List (Nat × Nat)) :
    cappedSum (k + 1) (shift ls) = mass ls + cappedSum k ls := by
  induction ls with
  | nil => rfl
  | cons p ps ih =>
    rcases p with ⟨H,w⟩
    change w * min (k + 1) (H + 1) + cappedSum (k + 1) (shift ps) =
      (w + mass ps) + (w * min k H + cappedSum k ps)
    rw [Nat.add_min_add_right, Nat.mul_add, Nat.mul_one, ih]
    omega

private theorem mass_layersOf (bs : List Nat) (h : binsAntitone bs) :
    mass (layersOf bs) = bs.headD 0 := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    change bs.headD 0 ≤ b ∧ binsAntitone bs at h
    change (b - bs.headD 0) + mass (shift (layersOf bs)) = b
    rw [mass_shift, ih h.2]
    exact Nat.sub_add_cancel h.1

theorem prefixCount_eq_cappedSum (k : Nat) (bs : List Nat) (h : binsAntitone bs) :
    prefixCount k bs = cappedSum k (layersOf bs) := by
  induction bs generalizing k with
  | nil =>
    cases k <;> rfl
  | cons b bs ih =>
    change bs.headD 0 ≤ b ∧ binsAntitone bs at h
    cases k with
    | zero => exact (cappedSum_zero _).symm
    | succ k =>
      change b + prefixCount k bs =
        (b - bs.headD 0) * min (k + 1) 1 + cappedSum (k + 1) (shift (layersOf bs))
      have hk : 1 ≤ k + 1 := by omega
      rw [Nat.min_eq_right hk, Nat.mul_one, cappedSum_shift k, mass_layersOf bs h.2, ih k h.2]
      omega

theorem prefixCount_joint {r s d e : Nat} (bs : List Nat) (hb : binsAntitone bs)
    (h : r + s ≤ 2 * (d + e)) :
    prefixCount r bs + prefixCount s bs ≤ 2 * (prefixCount d bs + prefixCount e bs) := by
  simp only [prefixCount_eq_cappedSum _ _ hb]
  exact cappedSum_joint (layersOf bs) h

#print axioms prefixCount_eq_cappedSum
#print axioms prefixCount_joint

end WidthThree.JointPool

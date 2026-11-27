import RotationPowers
import WordCoding

namespace CertifiedG449Rotation

open G449FiniteCoverage

def centerSwap (old x : Fin 4) : Fin 4 :=
  if x = old then 0 else if x = 0 then old else x

theorem centerSwap_injective : ∀ z x y : Fin 4,
    centerSwap z x = centerSwap z y → x = y := by decide +kernel

/-- Relabel the three noncentral colours by one of the six exact permutations.
The center colour is represented by 0 throughout. -/
def tailPerm (p : Fin 6) (x : Fin 4) : Fin 4 :=
  if x = 0 then 0 else Fin.ofNat 4 (perm p.val (x.val-1) + 1)

theorem tailPerm_injective : ∀ (p : Fin 6) (x y : Fin 4),
    tailPerm p x = tailPerm p y → x = y := by decide +kernel

theorem tailPerm_value : ∀ (p : Fin 6) (x : Fin 4), x ≠ 0 →
    (tailPerm p x).val - 1 = perm p.val (x.val-1) := by decide +kernel

theorem tailPerm_zero (p : Fin 6) : tailPerm p 0 = 0 := by simp [tailPerm]

def slot (i : Nat) : Nat := ring.getD i 0

private theorem all_slots_valid :
    (List.range 7).all (fun i => ring.contains (slot i)) = true := by decide +kernel

theorem slot_mem (i : Nat) (hi : i < 7) : slot i ∈ ring :=
  List.contains_iff_mem.mp (List.all_eq_true.mp all_slots_valid i (List.mem_range.mpr hi))

theorem slot_bound (i : Nat) (hi : i < 7) : slot i < 449 :=
  decide_eq_true_eq.mp (List.all_eq_true.mp checked_ring_labels.2.2 _ (slot_mem i hi))

theorem proper_near_center_ne_zero (f : Nat → Fin 4)
    (h : properGraph f) (hz : f center = 0) (i : Nat) (hi : i < 7) :
    f (slot i) ≠ 0 := by
  intro h'
  exact h center (slot i) checked_center.1 (slot_bound i hi)
    ((G449_central_neighbors_complete _ (slot_bound i hi)).mpr (slot_mem i hi)) (hz.trans h'.symm)

def colDigit (f : Nat → Fin 4) (i : Nat) : Nat := (f (slot i)).val-1

theorem colDigit_small (f : Nat → Fin 4) (i : Nat) : colDigit f i < 3 := by
  unfold colDigit
  have h := (f (slot i)).isLt
  omega

def colourWord (f : Nat → Fin 4) : Nat := encodeWord (colDigit f)

theorem colourWord_lt (f : Nat → Fin 4) : colourWord f < 2187 :=
  encodeWord_lt _ (fun i _ => colDigit_small f i)

theorem colourWord_digit (f : Nat → Fin 4) (i : Nat) (hi : i < 7) :
    label (colourWord f) i = colDigit f i :=
  encodeWord_decode _ (fun j _ => colDigit_small f j) i hi

def centerNormalized (f : Nat → Fin 4) : Nat → Fin 4 :=
  fun v => centerSwap (f center) (f v)

theorem centerNormalized_proper (f : Nat → Fin 4) (hf : properGraph f) :
    properGraph (centerNormalized f) := by
  intro a b ha hb he h
  exact hf a b ha hb he (centerSwap_injective _ _ _ h)

theorem centerNormalized_zero (f : Nat → Fin 4) : centerNormalized f center = 0 := by
  simp [centerNormalized,centerSwap]

def normalize (f : Nat → Fin 4) (r : Nat) (p : Fin 6) : Nat → Fin 4 :=
  fun v => tailPerm p (centerNormalized f (rotPower r v))

theorem normalize_proper (f : Nat → Fin 4) (hf : properGraph f) (r : Nat) (p : Fin 6) :
    properGraph (normalize f r p) := by
  have h := proper_comp_rotPower r _ (centerNormalized_proper f hf)
  intro a b ha hb he eq
  exact h a b ha hb he (tailPerm_injective p _ _ eq)

theorem normalize_center (f : Nat → Fin 4) (r : Nat) (p : Fin 6) :
    normalize f r p center = 0 := by
  simp only [normalize,rotPower_fixes_center,centerNormalized_zero,tailPerm_zero]

theorem normalize_word (f : Nat → Fin 4) (hf : properGraph f) (r : Nat) (p : Fin 6) :
    colourWord (normalize f r p) = transform (colourWord (centerNormalized f)) r p.val := by
  unfold colourWord transform encodeWord
  apply congrArg List.sum
  apply List.map_congr_left
  intro i hi
  have hb := List.mem_range.mp hi
  have ht : (i+r)%7 < 7 := by omega
  apply congrArg (fun x : Nat => x * 3^i)
  change (tailPerm p (centerNormalized f (rotPower r (slot i)))).val - 1 =
    perm p.val (label (colourWord (centerNormalized f)) ((i+r)%7))
  rw [show rotPower r (slot i) = slot ((i+r)%7) from rotPower_cycles_neighbors r i hb]
  have hy := proper_near_center_ne_zero (centerNormalized f) (centerNormalized_proper f hf)
    (centerNormalized_zero f) ((i+r)%7) ht
  rw [tailPerm_value p _ hy,colourWord_digit _ _ ht]
  rfl

/-- Every proper four-colouring can be rotated and relabelled into an
allowed published case while fixing the center colour to 0. -/
theorem proper_can_normalize (f : Nat → Fin 4) (hf : properGraph f) :
    ∃ c r, c < 6 ∧ r < 7 ∧ ∃ p : Fin 6,
      properGraph (normalize f r p) ∧ normalize f r p center = 0 ∧
      allowed c (colourWord (normalize f r p)) = true := by
  obtain ⟨c,r,p,hc,hr,hp,ha⟩ := orbit_case_coverage _ (colourWord_lt (centerNormalized f))
  let pp : Fin 6 := ⟨p,hp⟩
  refine ⟨c,r,hc,hr,pp,normalize_proper f hf r pp,normalize_center f r pp,?_⟩
  rw [normalize_word f hf r pp]
  exact ha

#print axioms normalize_word
#print axioms proper_can_normalize

end CertifiedG449Rotation

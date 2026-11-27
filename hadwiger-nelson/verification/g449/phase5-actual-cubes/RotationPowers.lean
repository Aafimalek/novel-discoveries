import RotationAutomorphism

namespace CertifiedG449Rotation

/-- The function sending each original vertex to its r-step rotated index. -/
def rotPower : Nat → Nat → Nat
  | 0, v => v
  | r+1, v => rot (rotPower r v)

theorem rotPower_bound (r v : Nat) (hv : v < 449) : rotPower r v < 449 := by
  induction r with
  | zero => exact hv
  | succ r ih => exact (rot_inv_on_published_vertices (rotPower r v) ih).1

theorem rotPower_adj_iff (r a b : Nat) (ha : a < 449) (hb : b < 449) :
    Adj (rotPower r a) (rotPower r b) ↔ Adj a b := by
  induction r with
  | zero => rfl
  | succ r ih =>
    exact (G449_rotation_automorphism _ _ (rotPower_bound r a ha) (rotPower_bound r b hb)).trans ih

theorem rotPower_fixes_center (r : Nat) : rotPower r center = center := by
  induction r with
  | zero => rfl
  | succ r ih =>
    change rot (rotPower r center) = center
    rw [ih, checked_center.2]

/-- Matches the finite coverage convention: input slot i+r modulo seven. -/
theorem rotPower_cycles_neighbors (r i : Nat) (hi : i < 7) :
    rotPower r (ring.getD i 0) = ring.getD ((i+r)%7) 0 := by
  induction r with
  | zero => simp [rotPower, Nat.mod_eq_of_lt hi]
  | succ r ih =>
    change rot (rotPower r (ring.getD i 0)) = ring.getD ((i+(r+1))%7) 0
    rw [ih, G449_central_neighbors_cycle _ (by omega)]
    have H : (((i+r)%7 + 1)%7) = (i+(r+1))%7 := by omega
    rw [H]

def properGraph (colour : Nat → Fin 4) : Prop :=
  ∀ a b : Nat, a < 449 → b < 449 → Adj a b → colour a ≠ colour b

/-- Every proper four-colouring remains proper after composition by any rotation power. -/
theorem proper_comp_rotPower (r : Nat) (c : Nat → Fin 4) (h : properGraph c) :
    properGraph (fun v => c (rotPower r v)) := by
  intro a b ha hb hab
  exact h _ _ (rotPower_bound r a ha) (rotPower_bound r b hb)
    ((rotPower_adj_iff r a b ha hb).mpr hab)

#print axioms rotPower_adj_iff
#print axioms rotPower_fixes_center
#print axioms rotPower_cycles_neighbors
#print axioms proper_comp_rotPower
end CertifiedG449Rotation

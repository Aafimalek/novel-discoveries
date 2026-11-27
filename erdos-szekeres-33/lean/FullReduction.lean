import OrientationClauses
import Signotope

namespace ES33

/-- Orientation is nonzero on every triple of distinct indices. -/
def GeneralPositionAll {n : ℕ} (p : Fin n ↪ Plane) : Prop :=
  ∀ i j k : Fin n, i ≠ j → i ≠ k → j ≠ k → orient (p i) (p j) (p k) ≠ 0

/-- The local real-geometric constraints on orientation signs listed in
increasing order of abscissae. -/
def SignotopeConstraints (n : ℕ) (χ : Fin n → Fin n → Fin n → Bool) : Prop :=
  ∀ a b c d : Fin n, a < b → b < c → c < d →
    let u := χ a b c
    let v := χ a b d
    let w := χ a c d
    let z := χ b c d
    (u ≤ v ∧ v ≤ w ∧ w ≤ z) ∨ (z ≤ w ∧ w ≤ v ∧ v ≤ u)

/-- An orientation-preserving shear allows sorting all points
by distinct first coordinates without changing any orientation bit. -/
def shear (t : ℝ) (p : Plane) : Plane := (p.1 + t*p.2, p.2)

@[simp] theorem orient_shear (t : ℝ) (a b c : Plane) :
    orient (shear t a) (shear t b) (shear t c) = orient a b c := by
  simp only [orient,shear]
  ring

private theorem exists_injective_shear_key {n : ℕ} (p : Fin n ↪ Plane) :
    ∃ t : ℝ, Function.Injective (fun i => (shear t (p i)).1) := by
  classical
  let bad : Finset ℝ := Finset.univ.image (fun ij : Fin n × Fin n =>
    ((p ij.2).1 - (p ij.1).1) / ((p ij.1).2 - (p ij.2).2))
  let L := insert (0 : ℝ) bad
  have Ln : L.Nonempty := ⟨0,Finset.mem_insert_self _ _⟩
  let t := L.max' Ln + 1
  refine ⟨t, fun i j h => ?_⟩
  by_cases hy : (p i).2 = (p j).2
  · apply p.injective
    apply Prod.ext
    · change (p i).1 + t * (p i).2 = (p j).1 + t * (p j).2 at h
      rw [hy] at h
      exact add_right_cancel h
    · exact hy
  · exfalso
    have hbad : t = ((p j).1 - (p i).1) / ((p i).2 - (p j).2) := by
      apply (eq_div_iff (sub_ne_zero.mpr hy)).2
      change (p i).1 + t * (p i).2 = (p j).1 + t * (p j).2 at h
      linear_combination h
    have hmem : t ∈ L := by
      change t ∈ insert 0 bad
      apply Finset.mem_insert_of_mem
      rw [hbad]
      exact Finset.mem_image.mpr ⟨(i,j),Finset.mem_univ _,rfl⟩
    exact (lt_irrefl t) ((L.le_max' _ hmem).trans_lt (lt_add_of_pos_right _ zero_lt_one))

private theorem exists_key_order {n : ℕ} (key : Fin n → ℝ) (hi : Function.Injective key) :
    ∃ f : Fin n ↪ Fin n, StrictMono (fun i => key (f i)) := by
  classical
  let D := Finset.univ.image key
  have hd : D.card = n := by simp [D,Finset.card_image_of_injective _ hi]
  let e := D.orderEmbOfFin hd
  have hit (i : Fin n) : ∃ j : Fin n, key j = e i := by
    obtain ⟨j,_,hj⟩ := Finset.mem_image.mp (D.orderEmbOfFin_mem hd i)
    exact ⟨j,hj⟩
  let perm : Fin n → Fin n := fun i => Classical.choose (hit i)
  have hperm (i : Fin n) : key (perm i) = e i := Classical.choose_spec (hit i)
  have hs : StrictMono (fun i => key (perm i)) := by
    intro a b hab
    change key (perm a) < key (perm b)
    rw [hperm a,hperm b]
    exact e.strictMono hab
  have hf : Function.Injective perm :=
    fun _ _ h => hs.injective (congrArg key h)
  exact ⟨⟨perm,hf⟩,hs⟩

/-- Every genuine counterexample gives a solution to the assignment problem
consisting of signotope and seven-set clauses. No satisfiability/realizability
converse is asserted. -/
theorem geometric_counterexample_gives_signotope {n : ℕ} (p : Fin n ↪ Plane)
    (gp : GeneralPositionAll p)
    (h : ¬ ∃ s : Finset Plane, s ⊆ Finset.univ.map p ∧ s.card = 7 ∧ ConvexPosition s) :
    ∃ χ : Fin n → Fin n → Fin n → Bool, SignotopeConstraints n χ ∧ AvoidanceClauses n χ := by
  classical
  obtain ⟨t,ht⟩ := exists_injective_shear_key p
  obtain ⟨f,hf⟩ := exists_key_order (fun i => (shear t (p i)).1) ht
  let q : Fin n ↪ Plane := f.trans p
  have gpq : GeneralPosition q := by
    intro a b c hab hbc
    exact gp (f a) (f b) (f c) (f.injective.ne hab.ne)
      (f.injective.ne (hab.trans hbc).ne) (f.injective.ne hbc.ne)
  refine ⟨orientations q, ?_, ?_⟩
  · intro a b c d hab hbc hcd
    have h1 : (shear t (q a)).1 < (shear t (q b)).1 := hf hab
    have h2 : (shear t (q b)).1 < (shear t (q c)).1 := hf hbc
    have h3 : (shear t (q c)).1 < (shear t (q d)).1 := hf hcd
    simpa only [orientations, orient_shear] using
      ordered_quad_signotope (shear t (q a)) (shear t (q b))
        (shear t (q c)) (shear t (q d)) h1 h2 h3
  · apply (no_heptagon_iff_orientation_clauses q gpq).mp
    rintro ⟨s,hs,hcard,hconv⟩
    apply h
    refine ⟨s,hs.trans ?_,hcard,hconv⟩
    intro x hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hx
    exact Finset.mem_map.mpr ⟨f i,Finset.mem_univ _,rfl⟩

/-- A sound transfer theorem for the exact first open case. An UNSAT
certificate for the displayed assignment problem would prove the 33-point
conjecture, but this theorem does not provide that certificate. -/
theorem es33_of_clause_unsat
    (unsat : ¬ ∃ χ : Fin 33 → Fin 33 → Fin 33 → Bool,
      SignotopeConstraints 33 χ ∧ AvoidanceClauses 33 χ)
    (p : Fin 33 ↪ Plane) (gp : GeneralPositionAll p) :
    ∃ s : Finset Plane, s ⊆ Finset.univ.map p ∧ s.card = 7 ∧ ConvexPosition s := by
  by_contra h
  exact unsat (geometric_counterexample_gives_signotope p gp h)

#print axioms orient_shear
#print axioms geometric_counterexample_gives_signotope
#print axioms es33_of_clause_unsat

end ES33

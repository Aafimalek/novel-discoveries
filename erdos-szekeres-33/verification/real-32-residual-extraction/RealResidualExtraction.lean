/- Static draft; not compiled while another task holds the Lean slot. -/
import GeometricReflectionLeader

namespace ES33.GeometricReflection

/-- Matching the signs in both triple orders prevents a nonzero
orientation in the source from becoming zero in the chart. -/
private theorem nonzero_of_two_bits {x y : ℝ}
    (forward : positiveBit x = positiveBit y)
    (reverse : positiveBit (-x) = positiveBit (-y))
    (hy : y ≠ 0) : x ≠ 0 := by
  intro hx
  rcases lt_or_gt_of_ne hy with hn | hp
  · have Y : positiveBit (-y) = true := by
      simpa only [positiveBit, decide_eq_true_eq] using neg_pos.mpr hn
    have X : 0 < -x := by
      simpa only [positiveBit, decide_eq_true_eq] using reverse.trans Y
    simp [hx] at X
  · have Y : positiveBit y = true := by
      simpa only [positiveBit, decide_eq_true_eq] using hp
    have X : 0 < x := by
      simpa only [positiveBit, decide_eq_true_eq] using forward.trans Y
    simp [hx] at X

/-- Keep the finite chart points from the actual normalization: the
residual is a real 32-label embedding, not merely an orientation model. -/
theorem es33_counterexample_gives_real_witness
    (p : Fin 33 ↪ Plane) (gp : GeneralPositionAll p)
    (h : ¬ ∃ s : Finset Plane, s ⊆ Finset.univ.map p ∧ s.card = 7 ∧ ConvexPosition s) :
    ∃ r : Fin 32 ↪ Plane, RealWitness r := by
  classical
  obtain ⟨f,q,hq,hsgn,ha⟩ := positive_anchor_exists (n := 32) p gp
  let χ : Anchor.Signs 33 := orientations (f.trans p)
  have sign_eq (i j k : Fin 33) :
      positiveBit (orient (q i) (q j) (q k)) = χ i j k := hsgn i j k
  have gp' : GeneralPosition (f.trans p) := by
    intro a b c hab hbc
    exact gp _ _ _ (f.injective.ne hab.ne)
      (f.injective.ne (hab.trans hbc).ne) (f.injective.ne hbc.ne)
  have holds_χ : SignotopeConstraints 33 χ := by
    intro a b c d hab hbc hcd
    simpa only [sign_eq] using ordered_quad_signotope (q a) (q b) (q c) (q d)
      (hq hab) (hq hbc) (hq hcd)
  have avoids_χ : AvoidanceClauses 33 χ := by
    apply (no_heptagon_iff_orientation_clauses (f.trans p) gp').mp
    rintro ⟨s,hs,hcard,hconv⟩
    apply h
    refine ⟨s,hs.trans ?_,hcard,hconv⟩
    intro x hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hx
    exact Finset.mem_map.mpr ⟨f i,Finset.mem_univ _,rfl⟩
  have anchor_χ : Anchor.Anchored χ := by
    intro i j hi hij
    rw [← sign_eq]
    simpa only [positiveBit, decide_eq_true_eq] using ha i j hi hij
  let r : Fin 32 ↪ Plane :=
    ⟨fun i => q i.succ, fun i j e =>
      Fin.succ_inj.mp (hq.injective (congrArg Prod.fst e))⟩
  have sorted_r : StrictMono (fun i => (r i).1) := by
    intro i j hij
    exact hq (Fin.succ_lt_succ_iff.mpr hij)
  have gp_r : GeneralPosition r := by
    intro i j k hij hjk
    let a : Fin 33 := i.succ
    let b : Fin 33 := j.succ
    let c : Fin 33 := k.succ
    have hy : orient (p (f a)) (p (f b)) (p (f c)) ≠ 0 :=
      gp' a b c (Fin.succ_lt_succ_iff.mpr hij) (Fin.succ_lt_succ_iff.mpr hjk)
    have rev_eq : positiveBit (-orient (q a) (q b) (q c)) =
        positiveBit (-orient (p (f a)) (p (f b)) (p (f c))) := by
      simpa only [orient_exchange (q a) (q b) (q c),
        orient_exchange (p (f a)) (p (f b)) (p (f c))] using hsgn a c b
    exact nonzero_of_two_bits (hsgn a b c) rev_eq hy
  have sign_r : orientations r = Anchor.residual χ := by
    funext a b c
    exact hsgn a.succ b.succ c.succ
  have old_no_even : ¬ Anchor.HasEvenSet χ 7 :=
    (Anchor.avoidanceClauses_iff χ).mp avoids_χ
  have split_even := Anchor.has_even_set_iff (n := 32) (k := 6) χ anchor_χ
  refine ⟨r,sorted_r,gp_r,?_⟩
  rw [sign_r]
  refine ⟨(Anchor.signotope_residual_iff χ anchor_χ).mp holds_χ,?_,?_⟩
  · exact (Anchor.avoidanceClauses_iff _).mpr
      (fun bad => old_no_even (split_even.mpr (Or.inl bad)))
  · exact fun bad => old_no_even (split_even.mpr (Or.inr bad))

/-- A real 33-point counterexample also gives a real residual witness
whose pair word satisfies the checked leader for any supplied list. -/
theorem es33_counterexample_gives_real_lex_witness
    (reps : List (Triple 32)) (p : Fin 33 ↪ Plane) (gp : GeneralPositionAll p)
    (h : ¬ ∃ s : Finset Plane, s ⊆ Finset.univ.map p ∧ s.card = 7 ∧ ConvexPosition s) :
    ∃ r : Fin 32 ↪ Plane, RealWitness r ∧
      ReflectionLex.Leader true (pairsWord reps (orientations r)) :=
  (real_lex_representative reps).mpr (es33_counterexample_gives_real_witness p gp h)

/-- Conditional direction only; no premise is proved here. -/
theorem es33_of_real_lex_witness_unsat (reps : List (Triple 32))
    (exclude : ¬ ∃ r : Fin 32 ↪ Plane, RealWitness r ∧
      ReflectionLex.Leader true (pairsWord reps (orientations r)))
    (p : Fin 33 ↪ Plane) (gp : GeneralPositionAll p) :
    ∃ s : Finset Plane, s ⊆ Finset.univ.map p ∧ s.card = 7 ∧ ConvexPosition s := by
  by_contra h
  exact exclude (es33_counterexample_gives_real_lex_witness reps p gp h)

#print axioms es33_counterexample_gives_real_witness
#print axioms es33_counterexample_gives_real_lex_witness
#print axioms es33_of_real_lex_witness_unsat

end ES33.GeometricReflection

import QuadrupleParity
import Mathlib.Data.Finset.Sort

namespace ES33

/-- No cryptographic oracle is involved. This is the mathematical truth
assignment to the ordered triple variables associated with a real point set. -/
noncomputable def orientations {n : ℕ} (p : Fin n ↪ Plane) (a b c : Fin n) : Bool :=
  positiveBit (orient (p a) (p b) (p c))

/-- General position, expressed only on increasing triples because all
other orderings are obtained by exchanging arguments. -/
def GeneralPosition {n : ℕ} (p : Fin n ↪ Plane) : Prop :=
  ∀ a b c : Fin n, a < b → b < c → orient (p a) (p b) (p c) ≠ 0

/-- One clause per seven indices: at least one of their thirty-five
four-subsets has nonconvex (odd) orientation parity. -/
def AvoidanceClauses (n : ℕ) (sgn : Fin n → Fin n → Fin n → Bool) : Prop :=
  ∀ t : Finset (Fin n), t.card = 7 →
    ∃ a ∈ t, ∃ b ∈ t, ∃ c ∈ t, ∃ d ∈ t, a < b ∧ b < c ∧ c < d ∧
      oddFour (sgn a b c) (sgn a b d) (sgn a c d) (sgn b c d) = true

private theorem preimage_submap {α β : Type*} (p : α ↪ β) (I : Finset α) {S : Finset β}
    (h : S ⊆ I.map p) : ∃ T ⊆ I, T.map p = S := by
  classical
  refine ⟨I.filter (fun x => p x ∈ S), Finset.filter_subset _ _, ?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hx
    exact (Finset.mem_filter.mp hi).2
  · intro hx
    obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp (h hx)
    exact Finset.mem_map.mpr ⟨i,Finset.mem_filter.mpr ⟨hi,hx⟩,rfl⟩

private theorem sorted_four {n : ℕ} (t : Finset (Fin n)) (h : t.card = 4) :
    ∃ a b c d : Fin n, a < b ∧ b < c ∧ c < d ∧ t = {a,b,c,d} := by
  let e := t.orderEmbOfFin h
  refine ⟨e 0,e 1,e 2,e 3,e.strictMono (by decide),e.strictMono (by decide),
    e.strictMono (by decide),?_⟩
  ext i
  constructor
  · intro hi
    obtain ⟨k,rfl⟩ := (Finset.range_orderEmbOfFin t h).superset hi
    fin_cases k <;> simp [e]
  · intro hi
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl
    all_goals exact t.orderEmbOfFin_mem h _

/-- The no-heptagon clause family is equivalent to geometric avoidance
on any fixed real realization, in particular at 33 points. This does not
assert the realizability of an arbitrary assignment of orientation bits. -/
theorem no_heptagon_iff_orientation_clauses {n : ℕ} (p : Fin n ↪ Plane)
    (gp : GeneralPosition p) :
    (¬ ∃ s : Finset Plane, s ⊆ Finset.univ.map p ∧ s.card = 7 ∧ ConvexPosition s) ↔
      AvoidanceClauses n (orientations p) := by
  classical
  constructor
  · intro h t ht
    obtain ⟨q,hq,hcard,hbad⟩ :=
      (no_heptagon_iff_every_seven_has_bad_four (Finset.univ.map p)).mp h
        (t.map p) (Finset.map_subset_map.mpr t.subset_univ) (by simpa using ht)
    obtain ⟨r,hrt,hrq⟩ := preimage_submap p t hq
    have hr : r.card = 4 := by simpa [← hrq] using hcard
    obtain ⟨a,b,c,d,hab,hbc,hcd,rfl⟩ := sorted_four r hr
    have hquad : q = ({p a,p b,p c,p d} : Finset Plane) := by
      rw [← hrq]
      simp
    refine ⟨a,hrt (by simp),b,hrt (by simp),c,hrt (by simp),d,hrt (by simp),hab,hbc,hcd,?_⟩
    exact (not_convex_quad_iff_odd_orientation (p a) (p b) (p c) (p d)
      (gp a b c hab hbc) (gp a b d hab (hbc.trans hcd))
      (gp a c d (hab.trans hbc) hcd) (gp b c d hbc hcd)).mp (hquad ▸ hbad)
  · intro h
    apply (no_heptagon_iff_every_seven_has_bad_four (Finset.univ.map p)).2
    intro s hs hcard
    obtain ⟨t,_,hts⟩ := preimage_submap p Finset.univ hs
    have ht : t.card = 7 := by simpa [← hts] using hcard
    obtain ⟨a,ha,b,hb,c,hc,d,hd,hab,hbc,hcd,hparity⟩ := h t ht
    have hsub : ({a,b,c,d} : Finset (Fin n)) ⊆ t := by
      intro x hx
      simp only [Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl
      exacts [ha,hb,hc,hd]
    have hquad : (({a,b,c,d} : Finset (Fin n)).map p) = {p a,p b,p c,p d} := by simp
    refine ⟨{p a,p b,p c,p d},hquad ▸ hts ▸ (Finset.map_subset_map.mpr hsub),?_ ,?_⟩
    · rw [← hquad, Finset.card_map]
      simp [Finset.card_insert_of_notMem,hab.ne,(hab.trans hbc).ne,
        (hab.trans (hbc.trans hcd)).ne,hbc.ne,(hbc.trans hcd).ne,hcd.ne]
    · exact (not_convex_quad_iff_odd_orientation (p a) (p b) (p c) (p d)
        (gp a b c hab hbc) (gp a b d hab (hbc.trans hcd))
        (gp a c d (hab.trans hbc) hcd) (gp b c d hbc hcd)).mpr hparity

/-- The exact 33-point specialization needed for a future UNSAT reduction. -/
theorem es33_counterexample_gives_assignment (p : Fin 33 ↪ Plane)
    (gp : GeneralPosition p)
    (h : ¬ ∃ s : Finset Plane, s ⊆ Finset.univ.map p ∧ s.card = 7 ∧ ConvexPosition s) :
    AvoidanceClauses 33 (orientations p) :=
  (no_heptagon_iff_orientation_clauses p gp).mp h

#print axioms no_heptagon_iff_orientation_clauses
#print axioms es33_counterexample_gives_assignment

end ES33

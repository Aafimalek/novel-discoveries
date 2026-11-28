/- Uncompiled actual-stack continuation. Algebra and adapter can be
checked independently first. -/
import RealDeterminantAdapter
import ES33.AnchoredTarget

namespace ES33.GeometricReflection

theorem mirror_twice (p : Plane) : mirror (mirror p) = p := by
  rcases p with ⟨x,y⟩
  simp [mirror]

private theorem mirror_inj : Function.Injective mirror := by
  intro p q h
  simpa only [mirror_twice] using congrArg mirror h

private def revEmb {n : ℕ} : Fin n ↪ Fin n :=
  ⟨Fin.rev, by
    intro a b h
    simpa only [Fin.rev_rev] using congrArg Fin.rev h⟩

/-- Mirror the coordinates and restore increasing x-order by reversing labels. -/
def reflected {n : ℕ} (p : Fin n ↪ Plane) : Fin n ↪ Plane :=
  ⟨fun a => mirror (p (Fin.rev a)), by
    intro a b h
    exact revEmb.injective (p.injective (mirror_inj h))⟩

def reverseSigns {n : ℕ} (χ : Anchor.Signs n) : Anchor.Signs n :=
  fun a b c => χ (Fin.rev c) (Fin.rev b) (Fin.rev a)

theorem orientations_reflected {n : ℕ} (p : Fin n ↪ Plane) :
    orientations (reflected p) = reverseSigns (orientations p) := by
  funext a b c
  change positiveBit (orient (mirror (p (Fin.rev a))) (mirror (p (Fin.rev b)))
      (mirror (p (Fin.rev c)))) =
    positiveBit (orient (p (Fin.rev c)) (p (Fin.rev b)) (p (Fin.rev a)))
  rw [orient_mirror_reverse]

theorem reflected_increasing {n : ℕ} (p : Fin n ↪ Plane)
    (hp : StrictMono (fun a => (p a).1)) :
    StrictMono (fun a => (reflected p a).1) := by
  intro a b hab
  change -(p (Fin.rev a)).1 < -(p (Fin.rev b)).1
  exact neg_lt_neg (hp (Fin.rev_lt_rev.mpr hab))

theorem reflected_generalPosition {n : ℕ} (p : Fin n ↪ Plane)
    (gp : GeneralPosition p) : GeneralPosition (reflected p) := by
  intro a b c hab hbc
  change orient (mirror (p (Fin.rev a))) (mirror (p (Fin.rev b)))
    (mirror (p (Fin.rev c))) ≠ 0
  rw [orient_mirror_reverse]
  exact gp _ _ _ (Fin.rev_lt_rev.mpr hbc) (Fin.rev_lt_rev.mpr hab)

private def revSet {n : ℕ} (t : Finset (Fin n)) : Finset (Fin n) :=
  t.map revEmb

private theorem mem_revSet {n : ℕ} {t : Finset (Fin n)} {i : Fin n} :
    i ∈ revSet t ↔ Fin.rev i ∈ t := by
  change i ∈ t.map revEmb ↔ Fin.rev i ∈ t
  constructor
  · intro h
    obtain ⟨j,hj,hij⟩ := Finset.mem_map.mp h
    change Fin.rev j = i at hij
    have e : j = Fin.rev i := by
      simpa only [Fin.rev_rev] using congrArg Fin.rev hij
    exact e ▸ hj
  · intro h
    exact Finset.mem_map.mpr ⟨Fin.rev i,h,Fin.rev_rev i⟩

private theorem card_revSet {n : ℕ} (t : Finset (Fin n)) :
    (revSet t).card = t.card :=
  Finset.card_map _

theorem reversal_signotope {n : ℕ} {χ : Anchor.Signs n}
    (hs : SignotopeConstraints n χ) :
    SignotopeConstraints n (reverseSigns χ) := by
  intro a b c d hab hbc hcd
  rcases hs (Fin.rev d) (Fin.rev c) (Fin.rev b) (Fin.rev a)
      (Fin.rev_lt_rev.mpr hcd) (Fin.rev_lt_rev.mpr hbc) (Fin.rev_lt_rev.mpr hab)
    with hu | hd
  · exact Or.inr hu
  · exact Or.inl hd

private theorem oddFour_reverse (a b c d : Bool) :
    oddFour d c b a = oddFour a b c d := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

theorem reversal_avoidance {n : ℕ} {χ : Anchor.Signs n}
    (h : AvoidanceClauses n χ) :
    AvoidanceClauses n (reverseSigns χ) := by
  intro t ht
  obtain ⟨a,ha,b,hb,c,hc,d,hd,hab,hbc,hcd,hodd⟩ :=
    h (revSet t) ((card_revSet t).trans ht)
  refine ⟨Fin.rev d,mem_revSet.mp hd,Fin.rev c,mem_revSet.mp hc,
    Fin.rev b,mem_revSet.mp hb,Fin.rev a,mem_revSet.mp ha,
    Fin.rev_lt_rev.mpr hcd,Fin.rev_lt_rev.mpr hbc,Fin.rev_lt_rev.mpr hab,?_⟩
  have hr : oddFour (χ b c d) (χ a c d) (χ a b d) (χ a b c) = true :=
    (oddFour_reverse _ _ _ _).trans hodd
  simpa only [reverseSigns,Fin.rev_rev] using hr

theorem reversal_no_positive {n k : ℕ} {χ : Anchor.Signs n}
    (h : ¬ Anchor.HasPositiveSet χ k) :
    ¬ Anchor.HasPositiveSet (reverseSigns χ) k := by
  rintro ⟨s,hs,hpos⟩
  refine h ⟨revSet s,(card_revSet s).trans hs,?_⟩
  intro a ha b hb c hc hab hbc
  have H := hpos (Fin.rev c) (mem_revSet.mp hc)
    (Fin.rev b) (mem_revSet.mp hb) (Fin.rev a) (mem_revSet.mp ha)
    (Fin.rev_lt_rev.mpr hbc) (Fin.rev_lt_rev.mpr hab)
  simpa only [reverseSigns,Fin.rev_rev] using H

/-- Concrete avoidance is transported through the already-proved parity
criterion; no new appeal to affine invariance of convex hulls is needed. -/
theorem reflected_no_heptagon {n : ℕ} (p : Fin n ↪ Plane) (gp : GeneralPosition p)
    (h : ¬ ∃ s : Finset Plane, s ⊆ Finset.univ.map p ∧ s.card = 7 ∧ ConvexPosition s) :
    ¬ ∃ s : Finset Plane, s ⊆ Finset.univ.map (reflected p) ∧ s.card = 7 ∧ ConvexPosition s := by
  apply (no_heptagon_iff_orientation_clauses _ (reflected_generalPosition p gp)).mpr
  rw [orientations_reflected]
  exact reversal_avoidance ((no_heptagon_iff_orientation_clauses p gp).mp h)

theorem reflected_residual32 (p : Fin 32 ↪ Plane)
    (h : Residual32 (orientations p)) :
    Residual32 (orientations (reflected p)) := by
  rw [orientations_reflected]
  exact ⟨reversal_signotope h.1,reversal_avoidance h.2.1,reversal_no_positive h.2.2⟩

/-- Orbit words used by the abstract guarded-leader theorem. No orbit
completeness assumption is needed merely to prove that the pairs swap. -/
abbrev Triple (n : ℕ) := Fin n × Fin n × Fin n

def tripleRev {n : ℕ} (t : Triple n) : Triple n :=
  (Fin.rev t.2.2,Fin.rev t.2.1,Fin.rev t.1)

private def signAt {n : ℕ} (χ : Anchor.Signs n) (t : Triple n) : Bool :=
  χ t.1 t.2.1 t.2.2

def pairsWord {n : ℕ} (reps : List (Triple n)) (χ : Anchor.Signs n) :
    List (Bool × Bool) :=
  reps.map fun t => (signAt χ t,signAt χ (tripleRev t))

theorem pairsWord_reflected {n : ℕ} (reps : List (Triple n)) (p : Fin n ↪ Plane) :
    pairsWord reps (orientations (reflected p)) =
      (pairsWord reps (orientations p)).map Prod.swap := by
  rw [orientations_reflected]
  simp [pairsWord,signAt,tripleRev,reverseSigns,Prod.swap,List.map_map,Function.comp_def]

#print axioms orient_mirror_reverse
#print axioms orientations_reflected
#print axioms reflected_no_heptagon
#print axioms reflected_residual32
#print axioms pairsWord_reflected

end ES33.GeometricReflection

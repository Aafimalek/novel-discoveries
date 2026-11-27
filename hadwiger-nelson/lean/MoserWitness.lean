import AlgebraicWitness

namespace PlaneColouring

private def zeroR : Radical4 := ⟨0,0,0,0⟩

/-- Standard seven-vertex Moser spindle, with the two diamonds sharing point 0.
Coordinate basis: 1, √3, √11, √33. -/
def moserPoints : Fin 7 → Coordinate
  | ⟨0, _⟩ => (zeroR, zeroR)
  | ⟨1, _⟩ => (⟨0,1,0,0⟩, zeroR)
  | ⟨2, _⟩ => (⟨0,1/2,0,0⟩, ⟨1/2,0,0,0⟩)
  | ⟨3, _⟩ => (⟨0,1/2,0,0⟩, ⟨-1/2,0,0,0⟩)
  | ⟨4, _⟩ => (⟨0,5/6,0,0⟩, ⟨0,0,0,1/6⟩)
  | ⟨5, _⟩ => (⟨0,5/12,1/12,0⟩, ⟨-5/12,0,0,1/12⟩)
  | ⟨6, _⟩ => (⟨0,5/12,-1/12,0⟩, ⟨5/12,0,0,1/12⟩)

def moserEdges : List (Fin 7 × Fin 7) :=
  [(0,2),(0,3),(1,2),(1,3),(2,3),
   (0,5),(0,6),(4,5),(4,6),(5,6),(1,4)]

/-- Eleven exact edges, checked by rational arithmetic inside the kernel. -/
theorem moser_edges_are_unit :
    ∀ e ∈ moserEdges, unitTest 3 11 (moserPoints e.1) (moserPoints e.2) = true := by
  intro e he
  simp only [moserEdges, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with he | he | he | he | he | he | he | he | he | he | he
  all_goals subst e; decide +kernel

/-- In a three-colouring the endpoints of a diamond must share a colour. -/
private theorem diamond_three_equal (p q a b : Fin 3)
    (pa : p ≠ a) (pb : p ≠ b) (qa : q ≠ a) (qb : q ≠ b) (ab : a ≠ b) :
    p = q := by
  revert pa pb qa qb ab
  fin_cases p <;> fin_cases q <;> fin_cases a <;> fin_cases b <;> decide +kernel

theorem moser_not_three :
    ¬ ∃ colour : Fin 7 → Fin 3, ∀ e ∈ moserEdges, colour e.1 ≠ colour e.2 := by
  rintro ⟨colour, hc⟩
  have cn : ∀ ab, ab ∈ moserEdges → colour ab.1 ≠ colour ab.2 := hc
  have h₁ : colour 0 = colour 1 := diamond_three_equal _ _ _ _
    (cn (0,2) (by decide)) (cn (0,3) (by decide)) (cn (1,2) (by decide))
    (cn (1,3) (by decide)) (cn (2,3) (by decide))
  have h₂ : colour 0 = colour 4 := diamond_three_equal _ _ _ _
    (cn (0,5) (by decide)) (cn (0,6) (by decide)) (cn (4,5) (by decide))
    (cn (4,6) (by decide)) (cn (5,6) (by decide))
  exact cn (1,4) (by decide) (h₁.symm.trans h₂)

/-- Smoke test of the generic witness checker, not a new bound. -/
theorem no_proper_three_moser : ¬ ∃ colour : Plane → Fin 3, Proper 3 colour :=
  no_plane_colouring_of_radical_witness 3 11 (by decide) (by decide)
    7 3 moserPoints moserEdges moser_edges_are_unit moser_not_three

#print axioms moser_edges_are_unit
#print axioms no_proper_three_moser

end PlaneColouring

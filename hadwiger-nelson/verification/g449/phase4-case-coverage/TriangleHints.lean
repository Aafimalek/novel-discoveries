import FourColourCNF

namespace CertifiedG449

/-- A triangle in a proper four-colouring cannot avoid a two-colour set. -/
theorem triangle_hits_colour_pair :
    ∀ a b c x y : Fin 4, a ≠ b → a ≠ c → b ≠ c → x ≠ y →
      a = x ∨ a = y ∨ b = x ∨ b = y ∨ c = x ∨ c = y := by
  decide +kernel

def triangle_hint (a b c : Nat) (x y : Fin 4) : List Int :=
  [(var a x : Int), (var a y : Int), (var b x : Int), (var b y : Int),
    (var c x : Int), (var c y : Int)]

/-- The exact six-literal triangle hint used by the G449 branches is
a consequence of a proper four-colouring. -/
theorem triangle_hint_of_proper (col : Nat → Fin 4) (a b c : Nat) (x y : Fin 4)
    (hab : col a ≠ col b) (hac : col a ≠ col c) (hbc : col b ≠ col c)
    (hxy : x ≠ y) :
    ∃ l ∈ triangle_hint a b c x y, litSat (assignment col) l := by
  have ok v d (h : col v = d) : litSat (assignment col) (var v d : Int) :=
    (litSat_pos_var _ _ _).mpr ((assignment_exact _ _ _).mpr h)
  rcases triangle_hits_colour_pair (col a) (col b) (col c) x y hab hac hbc hxy with
    q | q | q | q | q | q
  · exact ⟨(var a x : Int),by simp [triangle_hint],ok a x q⟩
  · exact ⟨(var a y : Int),by simp [triangle_hint],ok a y q⟩
  · exact ⟨(var b x : Int),by simp [triangle_hint],ok b x q⟩
  · exact ⟨(var b y : Int),by simp [triangle_hint],ok b y q⟩
  · exact ⟨(var c x : Int),by simp [triangle_hint],ok c x q⟩
  · exact ⟨(var c y : Int),by simp [triangle_hint],ok c y q⟩

#print axioms triangle_hits_colour_pair
#print axioms triangle_hint_of_proper
end CertifiedG449

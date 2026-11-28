import Init

namespace CyclotomicModSeven

abbrev F7 := Fin 7

/-- Equal-colour groups are {0,3}, {1,4}, {2,5}, {6}. -/
def group (r : F7) : Fin 4 :=
  match r.val with
  | 0 | 3 => 0
  | 1 | 4 => 1
  | 2 | 5 => 2
  | _ => 3

def allowedTrace (x : F7) : Prop := x = 1 ∨ x = 2 ∨ x = 5 ∨ x = 6

theorem norm_one_trace : ∀ a b : F7, a * b = 1 → allowedTrace (a+b) := by
  unfold allowedTrace
  decide +kernel

theorem trace_class_separates : ∀ x y : F7, allowedTrace (x-y) → group x ≠ group y := by
  unfold allowedTrace
  decide +kernel

/-- The finite-field obstruction: two evaluations of a unit difference are
reciprocal, so their trace cannot be an intra-colour difference. -/
theorem distinct_of_trace_norm (x y a b : F7) (norm_one : a*b = 1)
    (trace : x-y = a+b) : group x ≠ group y := by
  apply trace_class_separates
  rw [trace]
  exact norm_one_trace a b norm_one

#print axioms norm_one_trace
#print axioms trace_class_separates
#print axioms distinct_of_trace_norm

end CyclotomicModSeven

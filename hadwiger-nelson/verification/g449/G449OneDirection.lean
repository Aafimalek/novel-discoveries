import G449Data
namespace PlaneColouring.Cyclotomic42

/-- A representative of the first actual listed edge direction has unit length. -/
theorem first_direction_unit :
    dist (point (chosenDirections 0)) (point (fun _ => 0)) = 1 := by
  apply dist_one_of_normCoeffs table table_checked
  rw [show diff _ (fun _ => 0) = chosenDirections _ from funext (fun i => sub_zero _)]
  exact first_direction_checked

#print axioms first_direction_unit

end PlaneColouring.Cyclotomic42

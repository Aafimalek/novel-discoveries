import G449Data
namespace PlaneColouring.Cyclotomic42

set_option maxRecDepth 32768 in
set_option maxHeartbeats 25000000 in
theorem second_direction_checked : ∀ i, normCoeffs table (chosenDirections 1) i = (49^2 : ℤ) * start i := by
  decide +kernel

theorem second_direction_unit :
    dist (point (chosenDirections 1)) (point (fun _ => 0)) = 1 := by
  apply dist_one_of_normCoeffs table table_checked
  rw [show diff _ (fun _ => 0) = chosenDirections _ from funext (fun i => sub_zero _)]
  exact second_direction_checked

#print axioms second_direction_unit

end PlaneColouring.Cyclotomic42

import G449OneDirection
import G449Direction1
import G449SampleRows

namespace PlaneColouring.Cyclotomic42

theorem actual_rows_0_1_unit : dist (point (sampleRows 0)) (point (sampleRows 1)) = 1 := by
  have h : ∀ j, diff (sampleRows 0) (sampleRows 1) j = chosenDirections 0 j := by
    decide +kernel
  apply dist_one_of_normCoeffs table table_checked
  rw [show diff (sampleRows 0) (sampleRows 1) = chosenDirections 0 from funext h]
  exact first_direction_checked

theorem actual_rows_0_8_unit : dist (point (sampleRows 0)) (point (sampleRows 2)) = 1 := by
  have h : ∀ j, diff (sampleRows 0) (sampleRows 2) j = chosenDirections 1 j := by
    decide +kernel
  apply dist_one_of_normCoeffs table table_checked
  rw [show diff (sampleRows 0) (sampleRows 2) = chosenDirections 1 from funext h]
  exact second_direction_checked

#print axioms actual_rows_0_1_unit
#print axioms actual_rows_0_8_unit

end PlaneColouring.Cyclotomic42

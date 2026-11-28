import Mathlib.Basic.Real.Basic

namespace ES33

abbrev Plane := ℝ × ℝ

/-- Twice signed area for an ordered triple of planar points. -/
def orient (a b c : Plane) : ℝ :=
  (b.1-a.1)*(c.2-a.2) - (b.2-a.2)*(c.1-a.1)

end ES33

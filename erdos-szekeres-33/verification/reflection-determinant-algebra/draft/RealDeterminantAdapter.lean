/- Static adapter. Compiling ReflectionAlgebra.lean does not load this
import, so an ES33 stack timeout cannot obscure the algebra. -/
import ReflectionAlgebra
import ES33.TriangleOrientation

namespace ES33.GeometricReflection

abbrev mirror (p : Plane) : Plane := ReflectionAlgebra.mirror p

/-- The two determinant definitions actually agree definitionally. -/
theorem project_orient_eq (a b c : Plane) :
    ES33.orient a b c = ReflectionAlgebra.orient a b c := rfl

theorem orient_mirror (a b c : Plane) :
    ES33.orient (mirror a) (mirror b) (mirror c) = -ES33.orient a b c := by
  simpa only [project_orient_eq] using ReflectionAlgebra.orient_mirror a b c

theorem orient_mirror_reverse (a b c : Plane) :
    ES33.orient (mirror c) (mirror b) (mirror a) = ES33.orient a b c := by
  simpa only [project_orient_eq] using ReflectionAlgebra.orient_mirror_reverse a b c

#print axioms project_orient_eq
#print axioms orient_mirror
#print axioms orient_mirror_reverse

end ES33.GeometricReflection

import ExactEdges
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FieldSimp

namespace PlaneColouring

open Radical4

structure IntRadical4 where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ

abbrev IntCoordinate := IntRadical4 × IntRadical4

namespace IntRadical4

def scaled (N : ℤ) (x : IntRadical4) : Radical4 :=
  ⟨(x.a : ℚ)/N, (x.b : ℚ)/N, (x.c : ℚ)/N, (x.d : ℚ)/N⟩

def sub (x y : IntRadical4) : IntRadical4 :=
  ⟨x.a-y.a, x.b-y.b, x.c-y.c, x.d-y.d⟩

theorem scaled_sub (N : ℤ) (x y : IntRadical4) :
    scaled N (sub x y) = Radical4.sub (scaled N x) (scaled N y) := by
  simp only [scaled, sub, Radical4.sub, Int.cast_sub, sub_div]

end IntRadical4

noncomputable def scaledEmbed (r s N : ℤ) (p : IntCoordinate) : Plane :=
  coordinateEval r s (p.1.scaled N, p.2.scaled N)

/-- Mod 5, specialize √s to 1 and retain √r as the formal root of 3. -/
def modFiveColour (p : IntCoordinate) : ZMod 5 :=
  (p.1.a : ZMod 5) + (p.1.c : ZMod 5) +
  (p.2.a : ZMod 5) + (p.2.c : ZMod 5) + 2*((p.2.b : ZMod 5)+(p.2.d : ZMod 5))

set_option maxRecDepth 10240 in
set_option maxHeartbeats 1000000 in
private theorem modFiveTable : ∀ (a b c d t : ZMod 5),
    t ≠ 0 → a^2 + 3*b^2 + c^2 + 3*d^2 = t^2 → a*b + c*d = 0 →
      a+c+2*d ≠ 0 := by
  decide +kernel

/-- A single explicit proper five-colouring works for every fixed denominator
not divisible by five, whenever the independent radicands reduce to 3 and 1.
The result rules out an entire class of exact lattice searches for a
six- or seven-chromatic witness. -/
theorem modFiveColour_proper
    (r s N : ℤ) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hrat : ¬ IsSquare (r : ℚ)) (hsat : ¬ IsSquare (s : ℚ))
    (hrs : ¬ IsSquare ((r : ℚ)*(s : ℚ)))
    (hr5 : (r : ZMod 5) = 3) (hs5 : (s : ZMod 5) = 1)
    (hN : (N : ZMod 5) ≠ 0) (p q : IntCoordinate)
    (hu : dist (scaledEmbed r s N p) (scaledEmbed r s N q) = 1) :
    modFiveColour p ≠ modFiveColour q := by
  have hn : (N : ℚ) ≠ 0 := by
    intro hz
    have hz' : N = 0 := by exact_mod_cast hz
    exact hN (by simp [hz'])
  have hunit := (unitTest_iff_dist (r : ℚ) (s : ℚ)
    (by exact_mod_cast hr) (by exact_mod_cast hs) hrat hsat hrs _ _).mpr hu
  have eq := of_decide_eq_true hunit
  let x := p.1.sub q.1
  let y := p.2.sub q.2
  change add (sq (r : ℚ) (s : ℚ) (sub (p.1.scaled N) (q.1.scaled N)))
    (sq (r : ℚ) (s : ℚ) (sub (p.2.scaled N) (q.2.scaled N))) = one at eq
  rw [← IntRadical4.scaled_sub, ← IntRadical4.scaled_sub] at eq
  change add (sq (r : ℚ) (s : ℚ) (x.scaled N)) (sq (r : ℚ) (s : ℚ) (y.scaled N)) = one at eq
  have h0 := congrArg Radical4.a eq
  have h1 := congrArg Radical4.b eq
  have h2 := congrArg Radical4.c eq
  have h3 := congrArg Radical4.d eq
  simp only [Radical4.add,Radical4.sq,Radical4.one,IntRadical4.scaled] at h0 h1 h2 h3
  field_simp [hn] at h0 h1 h2 h3
  have h0' : x.a^2+r*x.b^2+s*x.c^2+r*s*x.d^2 +
      (y.a^2+r*y.b^2+s*y.c^2+r*s*y.d^2) = N^2 := by exact_mod_cast h0
  have h1'Q : (x.a:ℚ)*x.b+(s:ℚ)*x.c*x.d + ((y.a:ℚ)*y.b+(s:ℚ)*y.c*y.d) = 0 := by
    linear_combination h1/2
  have h2'Q : (x.a:ℚ)*x.c+(r:ℚ)*x.b*x.d + ((y.a:ℚ)*y.c+(r:ℚ)*y.b*y.d) = 0 := by
    linear_combination h2/2
  have h3'Q : (x.a:ℚ)*x.d+(x.b:ℚ)*x.c + ((y.a:ℚ)*y.d+(y.b:ℚ)*y.c) = 0 := by
    linear_combination h3/2
  have h1' : x.a*x.b+s*x.c*x.d + (y.a*y.b+s*y.c*y.d) = 0 := by exact_mod_cast h1'Q
  have h2' : x.a*x.c+r*x.b*x.d + (y.a*y.c+r*y.b*y.d) = 0 := by exact_mod_cast h2'Q
  have h3' : x.a*x.d+x.b*x.c + (y.a*y.d+y.b*y.c) = 0 := by exact_mod_cast h3'Q
  let cast5 := fun (i : ℤ) => (i : ZMod 5)
  have h0'' := congrArg cast5 h0'
  have h1'' := congrArg cast5 h1'
  have h2'' := congrArg cast5 h2'
  have h3'' := congrArg cast5 h3'
  dsimp [cast5] at h0'' h1'' h2'' h3''
  push_cast at h0'' h1'' h2'' h3''
  rw [hr5,hs5] at h0''
  rw [hs5] at h1''
  rw [hr5] at h2''
  have ha : ((x.a : ZMod 5)+(x.c : ZMod 5))^2
    + 3*((x.b : ZMod 5)+(x.d : ZMod 5))^2
    + ((y.a : ZMod 5)+(y.c : ZMod 5))^2
    + 3*((y.b : ZMod 5)+(y.d : ZMod 5))^2 = (N : ZMod 5)^2 := by
      linear_combination h0''+2*h2''
  have hb : ((x.a : ZMod 5)+(x.c : ZMod 5))*((x.b : ZMod 5)+(x.d : ZMod 5))
    + ((y.a : ZMod 5)+(y.c : ZMod 5))*((y.b : ZMod 5)+(y.d : ZMod 5)) = 0 := by
      linear_combination h1''+h3''
  intro hc
  apply modFiveTable _ _ _ _ _ hN ha hb
  have H : modFiveColour p - modFiveColour q = 0 := sub_eq_zero.mpr hc
  dsimp [modFiveColour] at H
  simp only [x,y,IntRadical4.sub,Int.cast_sub]
  linear_combination H

#print axioms modFiveTable
#print axioms modFiveColour_proper

end PlaneColouring

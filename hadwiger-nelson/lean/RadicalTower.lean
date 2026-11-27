import ExactEdges

namespace PlaneColouring

/-- Exact coefficients in an arbitrarily long nested radical basis.
A coefficient at a nonempty tower is A + B√r, where A and B are in the tail. -/
def Tower : List ℚ → Type
  | [] => ℚ
  | _ :: ts => Tower ts × Tower ts

namespace Tower

instance decEq (ts : List ℚ) : DecidableEq (Tower ts) := by
  induction ts with
  | nil => exact inferInstanceAs (DecidableEq ℚ)
  | cons r ts ih =>
    letI := ih
    exact inferInstanceAs (DecidableEq (Tower ts × Tower ts))

def zero : (ts : List ℚ) → Tower ts
  | [] => (0 : ℚ)
  | _ :: ts => (zero ts, zero ts)

def one : (ts : List ℚ) → Tower ts
  | [] => (1 : ℚ)
  | _ :: ts => (one ts, zero ts)

def add : (ts : List ℚ) → Tower ts → Tower ts → Tower ts
  | [], a, b => Rat.add a b
  | _ :: ts, (a,b), (c,d) => (add ts a c, add ts b d)

def sub : (ts : List ℚ) → Tower ts → Tower ts → Tower ts
  | [], a, b => Rat.sub a b
  | _ :: ts, (a,b), (c,d) => (sub ts a c, sub ts b d)

def scale (k : ℚ) : (ts : List ℚ) → Tower ts → Tower ts
  | [], a => Rat.mul k a
  | _ :: ts, (a,b) => (scale k ts a, scale k ts b)

def mul : (ts : List ℚ) → Tower ts → Tower ts → Tower ts
  | [], a, b => Rat.mul a b
  | r :: ts, (a,b), (c,d) =>
      (add ts (mul ts a c) (scale r ts (mul ts b d)),
        add ts (mul ts a d) (mul ts b c))

noncomputable def eval : (ts : List ℚ) → Tower ts → ℝ
  | [], a => Rat.cast (K := ℝ) a
  | r :: ts, (a,b) => eval ts a + eval ts b * Real.sqrt (r : ℝ)

@[simp] theorem eval_zero (ts : List ℚ) : eval ts (zero ts) = 0 := by
  induction ts with
  | nil => simp [eval,zero]
  | cons r ts ih => simp [eval,zero,ih]

@[simp] theorem eval_one (ts : List ℚ) : eval ts (one ts) = 1 := by
  induction ts with
  | nil => simp [eval,one]
  | cons r ts ih => simp [eval,one,ih]

@[simp] theorem eval_add (ts : List ℚ) (x y : Tower ts) :
    eval ts (add ts x y) = eval ts x + eval ts y := by
  induction ts with
  | nil => exact Rat.cast_add (α := ℝ) x y
  | cons r ts ih =>
    rcases x with ⟨a,b⟩
    rcases y with ⟨c,d⟩
    simp [eval,add,ih]
    ring

@[simp] theorem eval_sub (ts : List ℚ) (x y : Tower ts) :
    eval ts (sub ts x y) = eval ts x - eval ts y := by
  induction ts with
  | nil => exact Rat.cast_sub (α := ℝ) x y
  | cons r ts ih =>
    rcases x with ⟨a,b⟩
    rcases y with ⟨c,d⟩
    simp [eval,sub,ih]
    ring

@[simp] theorem eval_scale (k : ℚ) (ts : List ℚ) (x : Tower ts) :
    eval ts (scale k ts x) = (k : ℝ)*eval ts x := by
  induction ts with
  | nil => exact Rat.cast_mul (α := ℝ) k x
  | cons r ts ih =>
    rcases x with ⟨a,b⟩
    simp [eval,scale,ih]
    ring

@[simp] theorem eval_mul (ts : List ℚ) (nn : ∀ r ∈ ts, 0 ≤ r) (x y : Tower ts) :
    eval ts (mul ts x y) = eval ts x * eval ts y := by
  induction ts with
  | nil => exact Rat.cast_mul (α := ℝ) x y
  | cons r ts ih =>
    rcases x with ⟨a,b⟩
    rcases y with ⟨c,d⟩
    have n₁ : 0 ≤ (r : ℝ) := by exact_mod_cast (nn r (by simp))
    have n₂ : ∀ r ∈ ts, 0 ≤ r := fun r h => nn r (List.mem_cons_of_mem _ h)
    simp only [eval,mul,eval_add,eval_scale,ih n₂]
    linear_combination -(eval ts b * eval ts d)*Real.sq_sqrt n₁

end Tower

abbrev TowerPoint (ts : List ℚ) := Tower ts × Tower ts

noncomputable def towerEmbed (ts : List ℚ) (p : TowerPoint ts) : Plane :=
  !₂[Tower.eval ts p.1, Tower.eval ts p.2]

def towerUnitTest (ts : List ℚ) (p q : TowerPoint ts) : Bool :=
  let u := Tower.sub ts p.1 q.1
  let v := Tower.sub ts p.2 q.2
  decide (Tower.add ts (Tower.mul ts u u) (Tower.mul ts v v) = Tower.one ts)

/-- Exact arithmetic for unit-distance certificates works with any number of
radicals, with no algebraic independence theorem needed for edge soundness. -/
theorem dist_one_of_towerUnitTest (ts : List ℚ) (nn : ∀ r ∈ ts, 0 ≤ r)
    (p q : TowerPoint ts) (h : towerUnitTest ts p q = true) :
    dist (towerEmbed ts p) (towerEmbed ts q) = 1 := by
  have H := congrArg (Tower.eval ts) (of_decide_eq_true h)
  simp only [Tower.eval_add, Tower.eval_mul ts nn, Tower.eval_sub, Tower.eval_one] at H
  simp only [← pow_two] at H
  have D := EuclideanSpace.dist_sq_eq (towerEmbed ts p) (towerEmbed ts q)
  simp only [Fin.sum_univ_two,towerEmbed,Matrix.cons_val_zero,
    Matrix.cons_val_one,Real.dist_eq,sq_abs] at D
  rw [H] at D
  change dist (towerEmbed ts p) (towerEmbed ts q)^2 = 1 at D
  have nn' : 0 ≤ dist (towerEmbed ts p) (towerEmbed ts q) := dist_nonneg
  nlinarith

/-- Reusable endpoint for certificates in the actual unrestricted plane. -/
theorem chromatic_lower_of_tower_witness (ts : List ℚ) (nn : ∀ r ∈ ts, 0 ≤ r)
    (n k : ℕ) (pts : Fin n → TowerPoint ts) (edges : List (Fin n × Fin n))
    (euclidean : ∀ e ∈ edges, towerUnitTest ts (pts e.1) (pts e.2) = true)
    (unsat : ¬ ∃ colour : Fin n → Fin k, ∀ e ∈ edges, colour e.1 ≠ colour e.2) :
    ((k+1 : ℕ) : ℕ∞) ≤ planeGraph.chromaticNumber := by
  rw [planeGraph.le_chromaticNumber_iff_colorable]
  intro m hm
  by_contra! small
  have hmk : m ≤ k := by omega
  obtain ⟨c⟩ := hm
  apply unsat
  refine ⟨fun i => Fin.castLE hmk (c (towerEmbed ts (pts i))), ?_⟩
  intro e he hc
  exact c.valid (dist_one_of_towerUnitTest ts nn _ _ (euclidean e he))
    (Fin.castLE_injective hmk hc)

private def t11 (a b : ℚ) : Tower [11] := (a,b)
private def t511 (a b : Tower [11]) : Tower [5,11] := (a,b)
private def t3511 (a b : Tower [5,11]) : Tower [3,5,11] := (a,b)

/-- Product of the 30° rotation, (5+i√11)/6, and (2+i√5)/3.
This check exercises every layer of the three-radical coordinate format. -/
theorem threeRadical_rotation_unit :
    towerUnitTest [3,5,11]
      (t3511 (t511 (t11 0 (-1/18)) (t11 (-5/36) 0)) (t511 (t11 (5/18) 0) (t11 0 (-1/36))),
       t3511 (t511 (t11 (5/18) 0) (t11 0 (-1/36))) (t511 (t11 0 (1/18)) (t11 (5/36) 0)))
      (Tower.zero [3,5,11], Tower.zero [3,5,11]) = true := by decide +kernel

#print axioms threeRadical_rotation_unit
#print axioms dist_one_of_towerUnitTest
#print axioms chromatic_lower_of_tower_witness

end PlaneColouring

import Init

namespace WidthThree.LateHistogramBarrier

abbrev Label := Fin 9

/-- Label order is b,x₁,a,x₂,x₃,y₁,y₂,y₃,y₄. Branch rank is zero based;
the entry at a is a placeholder not used in the branch order. -/
def branchRank (other : Bool) (u : Label) : Nat :=
  let row := if other then [0,1,8,6,7,2,3,4,5] else [0,1,8,2,3,4,5,6,7]
  (row[u.val]?).getD 0

def rankAt (other : Bool) (cut : Nat) (u : Label) : Nat :=
  if u = 2 then cut
  else let r := branchRank other u
       r + if cut ≤ r then 1 else 0

/-- Four components, each weighted uniformly over the stated prefix of cuts.
They describe a valid antitone histogram on every induced branch order. -/
def components : List (Bool × Nat × Nat) :=
  [(false,3,2),(false,5,2),(false,8,1),(true,6,2)]

def count (p : Bool → Nat → Bool) : Nat :=
  (components.map fun (other,k,w) =>
    w * (((List.range (k+1)).filter (p other)).length)).sum

def total : Nat := count (fun _ _ => true)

def before (u v : Label) (p : Bool) (j : Nat) : Bool :=
  decide (rankAt p j u < rankAt p j v)

def fwdCount (u v : Label) : Nat := count (before u v)

def everyLabel (f : Label → Bool) : Bool := (List.finRange 9).all f

private theorem everyLabel_of_true {f : Label → Bool} (h : everyLabel f = true)
    (u : Label) : f u = true :=
  List.all_eq_true.mp h u (by simp)

theorem exact_mass_and_cut :
    total = 43 ∧ fwdCount 2 0 = 7 ∧ 6 * fwdCount 2 0 < total := by decide

/-- All 36 forward pairs in the late majority order exceed 2/3.
The reverse counts are at most 14, hence below 1/3. -/
theorem strong_forward_and_small_reverse (u v : Label) (h : u < v) :
    29 ≤ fwdCount u v ∧ fwdCount v u ≤ 14 := by
  let test (u v : Label) := decide (u < v → 29 ≤ fwdCount u v ∧ fwdCount v u ≤ 14)
  have htest : everyLabel (fun u => everyLabel (test u)) = true := by decide
  exact (of_decide_eq_true (everyLabel_of_true (everyLabel_of_true htest u) v)) h

theorem no_balanced_pair (u v : Label) (h : u ≠ v) :
    3 * fwdCount u v < total ∨ 2 * total < 3 * fwdCount u v := by
  by_cases hh : u < v
  · right
    have hn := (strong_forward_and_small_reverse u v hh).1
    exact Nat.lt_of_lt_of_le (by decide : 2 * total < 3 * 29) (Nat.mul_le_mul_left 3 hn)
  · have hvu : v < u := by
      have hle : v ≤ u := Nat.le_of_not_gt hh
      exact Nat.lt_of_le_of_ne hle (fun e => h (Fin.ext e.symm))
    left
    have hn := (strong_forward_and_small_reverse v u hvu).2
    exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_left 3 hn) (by decide : 3 * 14 < total)

/-- For a fixed weighted sample, the unnormalized XYZ inequality for two
comparisons sharing the centre on the same side. -/
def xyz (condition : Bool → Nat → Bool) (outgoing : Bool) (x u v : Label) : Prop :=
  let first := if outgoing then before x u else before u x
  let second := if outgoing then before x v else before v x
  count (fun p j => condition p j && first p j) *
    count (fun p j => condition p j && second p j) ≤
  count condition *
    count (fun p j => condition p j && first p j && second p j)

instance (condition : Bool → Nat → Bool) (outgoing : Bool) (x u v : Label) :
    Decidable (xyz condition outgoing x u v) := by unfold xyz; infer_instance

/-- Conditioning on b<a refutes realizability using XYZ: the two events
are x₂<a and y₂<a, with 36 trials, counts 14 and 9, and joint count 3. -/
theorem fails_conditional_xyz : ¬ xyz (before 0 2) false 2 3 6 := by decide

#print axioms exact_mass_and_cut
#print axioms no_balanced_pair
#print axioms fails_conditional_xyz

end WidthThree.LateHistogramBarrier

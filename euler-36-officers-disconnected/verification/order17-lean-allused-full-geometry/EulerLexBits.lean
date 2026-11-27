import Init

namespace EulerLexBits

def score : List Bool → Nat
  | [] => 0
  | b::l => (if b then 2^l.length else 0) + score l

theorem score_lt_power (l : List Bool) : score l < 2^l.length := by
  induction l with
  | nil => decide
  | cons b t ht =>
    cases b <;> simp only [score, Bool.false_eq_true, ↓reduceIte, List.length_cons, Nat.pow_succ] <;> omega

theorem score_same_length_drop {x y : List Bool} (hlen : x.length = y.length) :
    score (false::x) < score (true::y) := by
  have h := score_lt_power x
  simp only [score, Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
  rw [hlen] at h
  omega

theorem score_prefix_drop (p x y : List Bool)
    (hlen : x.length = y.length) (h : score x < score y) :
    score (p ++ x) < score (p ++ y) := by
  induction p with
  | nil => simpa using h
  | cons b p ih =>
    have he : (p ++ x).length = (p ++ y).length := by simp [hlen]
    change (if b then 2^(p++x).length else 0) + score (p++x) <
      (if b then 2^(p++y).length else 0) + score (p++y)
    rw [he]
    exact Nat.add_lt_add_left ih _

/-- Fixed-length binary objective strictly decreases at a common
prefix followed by an exchanged one and zero. -/
theorem score_first_difference (p x y : List Bool) (h : x.length = y.length) :
    score (p ++ false::x) < score (p ++ true::y) :=
  score_prefix_drop p (false::x) (true::y) (by simp [h]) (score_same_length_drop h)

#print axioms score_first_difference
end EulerLexBits

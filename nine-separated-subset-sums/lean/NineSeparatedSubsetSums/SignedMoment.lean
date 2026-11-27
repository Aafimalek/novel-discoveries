import Mathlib.Data.Int.Basic
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Tactic.Ring

namespace NineSeparatedSubsetSums

def spread (a : ℤ) (xs : List ℤ) : List ℤ :=
  xs.flatMap fun z => [z - a, z + a]

def signedSums : List ℤ → List ℤ
  | [] => [0]
  | a :: xs => spread a (signedSums xs)

theorem spread_length (a : ℤ) (xs : List ℤ) :
    (spread a xs).length = 2 * xs.length := by
  induction xs with
  | nil => simp [spread]
  | cons z xs ih =>
    simp [spread, List.flatMap_cons, show
      (List.flatMap (fun z => [z - a, z + a]) xs).length = 2 * xs.length from ih]
    omega

theorem signedSums_length (xs : List ℤ) : (signedSums xs).length = 2 ^ xs.length := by
  induction xs with
  | nil => simp [signedSums]
  | cons a xs ih =>
    simp only [signedSums, spread_length, ih, List.length_cons, pow_succ]
    omega

theorem spread_sum_sq (a : ℤ) (xs : List ℤ) :
    ((spread a xs).map (· ^ 2)).sum =
      2 * ((xs.map (· ^ 2)).sum + (xs.length : ℤ) * a^2) := by
  induction xs with
  | nil => simp [spread]
  | cons z xs ih =>
    simp only [spread, List.flatMap_cons, List.cons_append, List.nil_append,
      List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one] at *
    rw [ih]
    ring

theorem signedSums_sum_sq (xs : List ℤ) :
    ((signedSums xs).map (· ^ 2)).sum = (2 : ℤ)^xs.length * (xs.map (· ^ 2)).sum := by
  induction xs with
  | nil => simp [signedSums]
  | cons x xs ih =>
    rw [show signedSums (x :: xs) = spread x (signedSums xs) from rfl]
    rw [spread_sum_sq, ih, signedSums_length]
    simp only [List.map_cons, List.length_cons, List.sum_cons, pow_succ, Nat.cast_pow, Nat.cast_ofNat]
    ring

#print axioms spread_length
#print axioms signedSums_length
#print axioms spread_sum_sq
#print axioms signedSums_sum_sq

end NineSeparatedSubsetSums

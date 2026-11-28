import Init

namespace HadwigerNelson.F17Residue
set_option maxHeartbeats 3000000
set_option maxRecDepth 16000

abbrev Coord := Fin 17
abbrev Colour := Fin 6

def table : Array Nat := #[
  1420795925013344, 477990186980652, 620494401874016, 356590793606794, 710397936809169, 115049515615779, 920378492113240, 123868224342764, 1431042471286824, 193723753644301, 1549806921913425, 580891598496397, 359106561783964, 607859954069715, 934140582430232, 612652684587205, 1532319953668652
]

def color (a b : Coord) : Colour :=
  ⟨(((table[b.val]?).getD 0) / 8^a.val % 8) % 6, Nat.mod_lt _ (by decide)⟩

def normOne (a b : Coord) : Prop := (a.val*a.val+3*b.val*b.val)%17=1

instance (a b : Coord) : Decidable (normOne a b) := by
  unfold normOne
  infer_instance

def dirs : Array (Coord × Coord) := #[(1, 0), (2, 4), (2, 13), (5, 3), (5, 14), (7, 1), (7, 16), (8, 8), (8, 9), (9, 8), (9, 9), (10, 1), (10, 16), (12, 3), (12, 14), (15, 4), (15, 13), (16, 0)]

def direction (i : Fin 18) : Coord × Coord := (dirs[i.val]?).getD (0,0)

theorem hasDirection :
    ∀ (da db : Coord), normOne da db → ∃ i : Fin 18, direction i = (da, db) := by decide

def move (a d : Coord) : Coord := ⟨(a.val+d.val)%17, Nat.mod_lt _ (by decide)⟩

def diff (a a' : Coord) : Coord := ⟨(a'.val+17-a.val)%17, Nat.mod_lt _ (by decide)⟩

theorem move_diff : ∀ (a a' : Coord), move a (diff a a') = a' := by decide

def RowProper (b : Coord) : Prop :=
  ∀ (a : Coord) (i : Fin 18), color a b ≠ color (move a (direction i).1) (move b (direction i).2)

instance (b : Coord) : Decidable (RowProper b) := by
  unfold RowProper
  infer_instance

theorem row0 : RowProper 0 := by decide
theorem row1 : RowProper 1 := by decide
theorem row2 : RowProper 2 := by decide
theorem row3 : RowProper 3 := by decide
theorem row4 : RowProper 4 := by decide
theorem row5 : RowProper 5 := by decide
theorem row6 : RowProper 6 := by decide
theorem row7 : RowProper 7 := by decide
theorem row8 : RowProper 8 := by decide
theorem row9 : RowProper 9 := by decide
theorem row10 : RowProper 10 := by decide
theorem row11 : RowProper 11 := by decide
theorem row12 : RowProper 12 := by decide
theorem row13 : RowProper 13 := by decide
theorem row14 : RowProper 14 := by decide
theorem row15 : RowProper 15 := by decide
theorem row16 : RowProper 16 := by decide

theorem rowCover : ∀ (b : Coord), b = 0 ∨ b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 ∨ b = 5 ∨ b = 6 ∨ b = 7 ∨ b = 8 ∨ b = 9 ∨ b = 10 ∨ b = 11 ∨ b = 12 ∨ b = 13 ∨ b = 14 ∨ b = 15 ∨ b = 16 := by decide

theorem row_proper (b : Coord) : RowProper b := by
  rcases rowCover b with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact h.symm ▸ row0
  · exact h.symm ▸ row1
  · exact h.symm ▸ row2
  · exact h.symm ▸ row3
  · exact h.symm ▸ row4
  · exact h.symm ▸ row5
  · exact h.symm ▸ row6
  · exact h.symm ▸ row7
  · exact h.symm ▸ row8
  · exact h.symm ▸ row9
  · exact h.symm ▸ row10
  · exact h.symm ▸ row11
  · exact h.symm ▸ row12
  · exact h.symm ▸ row13
  · exact h.symm ▸ row14
  · exact h.symm ▸ row15
  · exact h.symm ▸ row16

theorem proper_unit_direction (a b da db : Coord) (h : normOne da db) :
    color a b ≠ color (move a da) (move b db) := by
  obtain ⟨i, hi⟩ := hasDirection da db h
  have good := row_proper b a i
  rw [hi] at good
  exact good

theorem proper_norm_one_difference (a b a' b' : Coord)
    (h : normOne (diff a a') (diff b b')) : color a b ≠ color a' b' := by
  have good := proper_unit_direction a b (diff a a') (diff b b') h
  rw [move_diff a a', move_diff b b'] at good
  exact good

#print axioms hasDirection
#print axioms row_proper
#print axioms proper_norm_one_difference

end HadwigerNelson.F17Residue

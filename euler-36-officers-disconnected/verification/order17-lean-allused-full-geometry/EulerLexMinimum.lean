import EulerLexMatrix

namespace LatinGap.PairEncoding

abbrev IncidenceSystem := Coord → BooleanMatrix
abbrev LabelPerms := Coord → Equiv.Perm (Fin 6)

def FixesPrefixes (starts : Coord → Nat) (p : LabelPerms) : Prop :=
  ∀ (g : Coord) (a : Fin 6), a.val < starts g → p g a = a

def pullIncidence (M : IncidenceSystem) (p : LabelPerms) : IncidenceSystem :=
  fun g a b => M g (p g a) (p (degreePartner g) b)

def swapFamily (p : LabelPerms) (g : Coord) (a b : Fin 6) : LabelPerms :=
  fun h => if h=g then (Equiv.swap a b).trans (p h) else p h

theorem swapFamily_fixes {starts : Coord → Nat} {p : LabelPerms}
    (hp : FixesPrefixes starts p) (g : Coord) (a b : Fin 6)
    (ha : starts g ≤ a.val) (hb : starts g ≤ b.val) :
    FixesPrefixes starts (swapFamily p g a b) := by
  intro j t ht
  by_cases eq : j=g
  · subst j
    have na : t≠a := fun e => by subst t; omega
    have nb : t≠b := fun e => by subst t; omega
    simp [swapFamily,Equiv.swap_apply_of_ne_of_ne na nb,hp g t ht]
  · simp [swapFamily,eq,hp j t ht]

def incidenceObjective (M : IncidenceSystem) : Nat :=
  matrixScore (M 0) * 4722366482869645213696 + matrixScore (M 2) * 68719476736 + matrixScore (M 3)

private theorem objective_first {Y X : IncidenceSystem}
    (h : matrixScore (Y 0) < matrixScore (X 0)) : incidenceObjective Y < incidenceObjective X := by
  have h2 := matrixScore_bound (Y 2)
  have h3 := matrixScore_bound (Y 3)
  unfold incidenceObjective
  omega

private theorem objective_second {Y X : IncidenceSystem} (e : Y 0 = X 0)
    (h : matrixScore (Y 2) < matrixScore (X 2)) : incidenceObjective Y < incidenceObjective X := by
  have h3 := matrixScore_bound (Y 3)
  unfold incidenceObjective
  rw [e]
  omega

private theorem objective_third {Y X : IncidenceSystem} (e : Y 0 = X 0) (e2 : Y 2 = X 2)
    (h : matrixScore (Y 3) < matrixScore (X 3)) : incidenceObjective Y < incidenceObjective X := by
  unfold incidenceObjective
  rw [e,e2]
  omega

set_option maxHeartbeats 1500000 in
/-- If a row of any of the four required incidence systems is inverted,
swap its labels. For group 1 this is a column swap of the primary
matrix; groups 2 and 3 cannot disturb earlier scored matrices. -/
theorem incidenceObjective_swap_drop (M : IncidenceSystem) (p : LabelPerms)
    (sym : ∀ a b : Fin 6, M 1 b a = M 0 a b)
    (g : Coord) (a b k : Fin 6) (ab : a<b)
    (earlier : ∀ t : Fin 6, t<k → pullIncidence M p g a t=pullIncidence M p g b t)
    (ha : pullIncidence M p g a k=true) (hb : pullIncidence M p g b k=false) :
    incidenceObjective (pullIncidence M (swapFamily p g a b)) < incidenceObjective (pullIncidence M p) := by
  have transpose (a b : Fin 6) : pullIncidence M p 1 b a = pullIncidence M p 0 a b := by
    change M 1 (p 1 b) (p 0 a) = M 0 (p 0 a) (p 1 b)
    exact sym _ _
  have cover : ∀ g : Coord, g=0 ∨ g=1 ∨ g=2 ∨ g=3 := by decide
  rcases cover g with rfl | rfl | rfl | rfl
  · apply objective_first
    have eq : pullIncidence M (swapFamily p 0 a b) 0 =
        fun i j => pullIncidence M p 0 (Equiv.swap a b i) j := by funext i j; rfl
    rw [eq]
    exact matrixScore_row_swap_drop _ a b k ab earlier ha hb
  · apply objective_first
    have eq : pullIncidence M (swapFamily p 1 a b) 0 =
        fun i j => pullIncidence M p 0 i (Equiv.swap a b j) := by funext i j; rfl
    rw [eq]
    exact matrixScore_col_swap_drop _ a b k ab
      (fun t h => (transpose t a).symm.trans ((earlier t h).trans (transpose t b)))
      ((transpose k a).symm.trans ha) ((transpose k b).symm.trans hb)
  · apply objective_second
    · funext i j; rfl
    · have eq : pullIncidence M (swapFamily p 2 a b) 2 =
          fun i j => pullIncidence M p 2 (Equiv.swap a b i) j := by funext i j; rfl
      rw [eq]
      exact matrixScore_row_swap_drop _ a b k ab earlier ha hb
  · apply objective_third
    · funext i j; rfl
    · funext i j; rfl
    · have eq : pullIncidence M (swapFamily p 3 a b) 3 =
          fun i j => pullIncidence M p 3 (Equiv.swap a b i) j := by funext i j; rfl
      rw [eq]
      exact matrixScore_row_swap_drop _ a b k ab earlier ha hb

/-- Existence of simultaneous lex normalization without enumerating
permutations; minimize the finite row-major objective, then rule out
any bad exchange by strict improvement. -/
theorem exists_simultaneous_lex (M : IncidenceSystem) (starts : Coord → Nat)
    (sym : ∀ a b : Fin 6, M 1 b a = M 0 a b) :
    ∃ p : LabelPerms, FixesPrefixes starts p ∧
      ∀ (g : Coord) (a b : Fin 6), starts g ≤ a.val → a<b →
        firstDifferenceOrder (pullIncidence M p g) a b := by
  classical
  let P (n : Nat) := ∃ p : LabelPerms, FixesPrefixes starts p ∧ incidenceObjective (pullIncidence M p) = n
  have found : ∃ n, P n :=
    ⟨_,fun _ => Equiv.refl _,fun _ _ _ => rfl,rfl⟩
  obtain ⟨p,fix,minimal⟩ := Nat.find_spec found
  refine ⟨p,fix,?_⟩
  intro g a b ha ab k before left
  cases e : pullIncidence M p g b k
  · exfalso
    have hb : starts g ≤ b.val := ha.trans (Nat.le_of_lt ab)
    have alt : P (incidenceObjective (pullIncidence M (swapFamily p g a b))) :=
      ⟨_,swapFamily_fixes fix g a b ha hb,rfl⟩
    have hn := Nat.find_min' found alt
    have drop := incidenceObjective_swap_drop M p sym g a b k ab before left e
    omega
  · rfl

#print axioms exists_simultaneous_lex
end LatinGap.PairEncoding

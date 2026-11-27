import EulerAllUsedLex
import EulerLexBits

namespace LatinGap.PairEncoding

abbrev BooleanMatrix := Fin 6 → Fin 6 → Bool

def firstDifferenceOrder (M : BooleanMatrix) (a b : Fin 6) : Prop :=
  ∀ k : Fin 6, (∀ t : Fin 6, t<k → M a t=M b t) → M a k=true → M b k=true

def rowIndex (q : Fin 36) : Fin 6 := ⟨q.val/6,by have := q.isLt; omega⟩
def colIndex (q : Fin 36) : Fin 6 := ⟨q.val%6,by omega⟩

def matrixScore (M : BooleanMatrix) : Nat :=
  EulerLexBits.score (List.ofFn fun q : Fin 36 => M (rowIndex q) (colIndex q))

theorem matrixScore_bound (M : BooleanMatrix) : matrixScore M < 68719476736 := by
  simpa [matrixScore] using EulerLexBits.score_lt_power (List.ofFn fun q : Fin 36 => M (rowIndex q) (colIndex q))

theorem ofFn_first_difference {n : Nat} (U V : Fin n → Bool)
    (k : Fin n) (earlier : ∀ j : Fin n, j<k → U j=V j) (hU : U k=false) (hV : V k=true) :
    EulerLexBits.score (List.ofFn U) < EulerLexBits.score (List.ofFn V) := by
  induction n with
  | zero => exact Fin.elim0 k
  | succ n ih =>
    rw [List.ofFn_succ,List.ofFn_succ]
    refine Fin.cases ?_ (fun t => ?_) k earlier hU hV
    · intro _ hu hv
      rw [hu,hv]
      exact EulerLexBits.score_same_length_drop (by simp)
    · intro ent hu hv
      have e : U 0=V 0 := ent 0 (by simp)
      rw [e]
      change EulerLexBits.score ([V 0] ++ List.ofFn (fun i => U i.succ)) <
        EulerLexBits.score ([V 0] ++ List.ofFn (fun i => V i.succ))
      apply EulerLexBits.score_prefix_drop _ _ _ (by simp)
      exact ih (fun i => U i.succ) (fun i => V i.succ) t
        (fun u hu' => ent u.succ (Fin.succ_lt_succ_iff.mpr hu')) hu hv

private theorem row_div_mod (a k : Fin 6) :
    rowIndex ⟨6*a.val+k.val,by have := a.isLt; have := k.isLt; omega⟩ = a ∧
    colIndex ⟨6*a.val+k.val,by have := a.isLt; have := k.isLt; omega⟩ = k := by
  have ha := a.isLt
  have hk := k.isLt
  constructor <;> apply Fin.ext
  · change (6*a.val+k.val)/6 = a.val
    omega
  · change (6*a.val+k.val)%6 = k.val
    omega

private theorem index_decomp (q : Fin 36) :
    6*(rowIndex q).val+(colIndex q).val=q.val := by
  change 6*(q.val/6)+q.val%6=q.val
  omega

theorem matrixScore_row_swap_drop (M : BooleanMatrix) (a b k : Fin 6) (ab : a<b)
    (earlier : ∀ t : Fin 6, t<k → M a t=M b t) (ha : M a k=true) (hb : M b k=false) :
    matrixScore (fun i j => M (Equiv.swap a b i) j) < matrixScore M := by
  let q : Fin 36 := ⟨6*a.val+k.val, by have := a.isLt; have := k.isLt; omega⟩
  have hq : rowIndex q=a ∧ colIndex q=k := row_div_mod a k
  unfold matrixScore
  apply ofFn_first_difference _ _ q
  · intro u hu
    let i := rowIndex u
    let j := colIndex u
    change M (Equiv.swap a b i) j = M i j
    have hdecomp := index_decomp u
    change 6*i.val+j.val=u.val at hdecomp
    have before : 6*i.val+j.val < 6*a.val+k.val := by simpa [q,hdecomp] using (show u.val < q.val from hu)
    have hi : i.val ≤ a.val := by have := k.isLt; omega
    have bne : i ≠ b := by intro e; exact (Nat.not_le_of_lt ab) ((congrArg Fin.val e) ▸ hi)
    by_cases eq : i=a
    · rw [eq] at before ⊢
      rw [Equiv.swap_apply_left]
      exact (earlier j (show j.val < k.val by omega)).symm
    · rw [Equiv.swap_apply_of_ne_of_ne eq bne]
  · simp [hq.1,hq.2,hb]
  · simp [hq.1,hq.2,ha]

/-- Column swaps drop the same row-major objective: before the first
distinguishing row, both columns have identical bits. -/
theorem matrixScore_col_swap_drop (M : BooleanMatrix) (a b k : Fin 6) (ab : a<b)
    (earlier : ∀ t : Fin 6, t<k → M t a=M t b) (ha : M k a=true) (hb : M k b=false) :
    matrixScore (fun i j => M i (Equiv.swap a b j)) < matrixScore M := by
  let q : Fin 36 := ⟨6*k.val+a.val, by have := a.isLt; have := k.isLt; omega⟩
  have hq : rowIndex q=k ∧ colIndex q=a := row_div_mod k a
  unfold matrixScore
  apply ofFn_first_difference _ _ q
  · intro u hu
    let i := rowIndex u
    let j := colIndex u
    change M i (Equiv.swap a b j) = M i j
    have hdecomp := index_decomp u
    change 6*i.val+j.val=u.val at hdecomp
    have before : 6*i.val+j.val < 6*k.val+a.val := by simpa [q,hdecomp] using (show u.val < q.val from hu)
    have hi : i.val ≤ k.val := by have := a.isLt; omega
    by_cases hh : i<k
    · by_cases ja : j=a
      · rw [ja,Equiv.swap_apply_left,earlier i hh]
      · by_cases jb : j=b
        · rw [jb,Equiv.swap_apply_right,earlier i hh]
        · rw [Equiv.swap_apply_of_ne_of_ne ja jb]
    · have ie : i=k := Fin.ext (by have z : ¬i.val<k.val := hh; omega)
      have jt : j.val<a.val := by rw [ie] at before; omega
      have ja : j≠a := fun ej => (Nat.ne_of_lt jt) (congrArg Fin.val ej)
      have jb : j≠b := fun ej => (Nat.ne_of_lt (jt.trans ab)) (congrArg Fin.val ej)
      rw [Equiv.swap_apply_of_ne_of_ne ja jb]
  · simp [hq.1,hq.2,hb]
  · simp [hq.1,hq.2,ha]

#print axioms matrixScore_row_swap_drop
#print axioms matrixScore_col_swap_drop
end LatinGap.PairEncoding

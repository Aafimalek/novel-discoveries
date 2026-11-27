import EulerArchivePrefix
import EulerArchivedCounterValuation

namespace LatinGap.PairEncoding

private theorem literal_allowed {Q : ℕ → Prop} (id : ℕ) (sign : Bool)
    (pos : 0<id) (allowed : Q id) : Q (literal id sign).natAbs := by
  rw [(literal_spec pos sign).2.1]
  exact allowed

/-- A numeric counter's only variable occurrences are its bounded grid
states and its declared input bits. -/
theorem numericSequentialBlock_variables (m k base : ℕ) (idx : ℕ → ℕ) (sign : Bool)
    (hk : 0<k) (posBase : 0<base) (posInput : ∀ i<m+k,0<idx i)
    (Q : ℕ → Prop) (input : ∀ i<m+k,Q (idx i))
    (state : ∀ r<m, ∀ j<k,Q (numericStateNumber base k r j)) :
    ∀ c ∈ numericSequentialBlock m k base idx sign, ∀ l∈c, Q l.natAbs := by
  let x (i : ℕ) := literal (idx i) (!sign)
  let s (r j : ℕ) (b : Bool) := literal (numericStateNumber base k r j) b
  have qx (i : ℕ) (hi : i<m+k) : Q (x i).natAbs :=
    literal_allowed _ _ (posInput i hi) (input i hi)
  have qs (r j : ℕ) (hr : r<m) (hj : j<k) (b : Bool) : Q (s r j b).natAbs :=
    literal_allowed _ _ (by unfold numericStateNumber; omega) (state r hr j hj)
  intro c hc l hl
  obtain ⟨r,hr,hR⟩ := List.mem_flatMap.mp hc
  have rlt := List.mem_range.mp hr
  rcases List.mem_cons.mp hR with eq | more
  · subst c
    change l∈[x r,s r 0 true] at hl
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hl
    rcases hl with rfl|rfl
    · exact qx r (by omega)
    · exact qs r 0 rlt hk true
  · obtain ⟨j,hj,H⟩ := List.mem_flatMap.mp more
    have jlt := List.mem_range.mp hj
    rcases List.mem_append.mp H with hor | step
    · by_cases h : r+1<m
      · simp only [ite_eq_left h,List.mem_singleton] at hor
        subst c
        change l∈[s r j false,s (r+1) j true] at hl
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hl
        rcases hl with rfl|rfl
        · exact qs r j rlt jlt false
        · exact qs (r+1) j h jlt true
      · simp [h] at hor
    · by_cases h : j+1<k
      · simp only [ite_eq_left h,List.mem_singleton] at step
        subst c
        change l∈[x (r+j+1),s r j false,s r (j+1) true] at hl
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hl
        rcases hl with rfl|rfl|rfl
        · exact qx _ (by omega)
        · exact qs r j rlt jlt false
        · exact qs r _ rlt h true
      · simp only [ite_eq_right h,List.mem_singleton] at step
        subst c
        change l∈[x (r+k),s r j false] at hl
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hl
        rcases hl with rfl|rfl
        · exact qx _ (by omega)
        · exact qs r j rlt jlt false

private theorem hold_of_value_agreement (v w : ℕ → Bool) (c : List ℤ)
    (agree : ∀ l∈c, w l.natAbs = v l.natAbs)
    (h : NumberedHolds v c) : NumberedHolds w c := by
  obtain ⟨l,hl,h0,he⟩ := h
  exact ⟨l,hl,h0,(agree l hl).trans he⟩

private theorem archivedProjectionCounter_variables :
    ∀ c∈archiveProjectionCountBlock, ∀ l∈c, l.natAbs≤1512 ∨ 9073≤l.natAbs := by
  intro c h
  rcases List.mem_append.mp h with hc | hc
  · refine numericSequentialBlock_variables 17 19 9073 projectionCounterId false (by decide)
      (by decide) (fun i _ => by unfold projectionCounterId; omega) (fun i => i≤1512 ∨ 9073≤i) ?_ ?_ c hc
    · intro i hi
      left
      unfold projectionCounterId
      omega
    · intro r hr j hj
      right
      unfold numericStateNumber
      omega
  · refine numericSequentialBlock_variables 19 17 9396 projectionCounterId true (by decide)
      (by decide) (fun i _ => by unfold projectionCounterId; omega) (fun i => i≤1512 ∨ 9073≤i) ?_ ?_ c hc
    · intro i hi
      left
      unfold projectionCounterId
      omega
    · intro r hr j hj
      right
      unfold numericStateNumber
      omega

private theorem archivedDegreeExcessCounter_variables (g : Coord) :
    ∀ c∈archiveDegreeExcessCountBlock g, ∀ l∈c, l.natAbs≤1512 ∨ 9073≤l.natAbs := by
  have lo (i : ℕ) : 9719 ≤ degreeExcessCounterId g i := (degreeThresholdNumber_bounds _ _ _).1
  intro c h
  rcases List.mem_append.mp h with hc | hc
  · refine numericSequentialBlock_variables 5 19 (9887+190*g.val) (degreeExcessCounterId g)
      false (by omega) (by omega) (fun i _ => by have := lo i; omega) (fun i => i≤1512 ∨ 9073≤i) ?_ ?_ c hc
    · intro i _
      right
      have := lo i
      omega
    · intro r hr j hj
      right
      unfold numericStateNumber
      omega
  · refine numericSequentialBlock_variables 19 5 (9982+190*g.val) (degreeExcessCounterId g)
      true (by omega) (by omega) (fun i _ => by have := lo i; omega) (fun i => i≤1512 ∨ 9073≤i) ?_ ?_ c hc
    · intro i _
      right
      have := lo i
      omega
    · intro r hr j hj
      right
      unfold numericStateNumber
      omega

/-- One actual DIMACS valuation satisfies the full common support and count
clause blocks simultaneously, preserving every input for the remaining
degree/profile/cut clauses. -/
theorem geometry_satisfies_archived_prefix_and_cardinality (D : Design 6)
    (linear : Linear D) (sat : Saturated D) (size : D.card=17)
    (minimum : ∀ g : Coord, ∀ a : Fin 6, 2≤freq D (g,a))
    (v : ℕ → Bool)
    (hword : ∀ w : Word 6, v (wordNumber w) = (encode D).select w)
    (hpair : ∀ p : PairKey 6, v (pairNumber p) = (encode D).pair p)
    (hdeg : ∀ g : Coord, ∀ a : Fin 6, ∀ d : Fin 7,
      v (degreeThresholdNumber g a d) = decide (d.val≤freq D (g,a))) :
    ∃ w : ℕ → Bool,
      (∀ i, i≤1512 ∨ (9719≤i ∧ i≤9886) → w i=v i) ∧
      (∀ c∈archivedSupportPrefix, NumberedHolds w c) ∧
      (∀ c∈archiveProjectionCountBlock, NumberedHolds w c) ∧
      ∀ g : Coord, ∀ c∈archiveDegreeExcessCountBlock g, NumberedHolds w c := by
  obtain ⟨u,keepU,p17,p5⟩ := geometry_satisfies_archived_cardinality
    D linear size minimum v hpair hdeg
  have huWord (w : Word 6) : u (wordNumber w) = (encode D).select w :=
    (keepU _ (Or.inl (by have := (wordNumber_bounds w).2; omega))).trans (hword w)
  have huPair (p : PairKey 6) : u (pairNumber p) = (encode D).pair p :=
    (keepU _ (Or.inl (by have := (pairNumber_bounds p).2; omega))).trans (hpair p)
  obtain ⟨w,keepW,hPrefix⟩ := geometry_satisfies_archived_support_prefix D linear sat u huWord huPair
  refine ⟨w,?_,hPrefix,?_,?_⟩
  · intro i h
    have hw : i≤1512 ∨ 9073≤i := by omega
    have hu : i≤9072 ∨ (9719≤i ∧ i≤9886) := by omega
    exact (keepW i hw).trans (keepU i hu)
  · intro c hc
    exact hold_of_value_agreement u w c
      (fun l hl => keepW _ (archivedProjectionCounter_variables c hc l hl)) (p17 c hc)
  · intro g c hc
    exact hold_of_value_agreement u w c
      (fun l hl => keepW _ (archivedDegreeExcessCounter_variables g c hc l hl)) (p5 g c hc)

#print axioms numericSequentialBlock_variables
#print axioms geometry_satisfies_archived_prefix_and_cardinality

end LatinGap.PairEncoding

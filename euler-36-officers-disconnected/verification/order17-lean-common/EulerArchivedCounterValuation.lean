import EulerNumberedCounters

namespace LatinGap.PairEncoding

structure ArchivedGridSpec where
  base : ℕ
  rows : ℕ
  cols : ℕ

def archivedGrid (q : Fin 10) : ArchivedGridSpec :=
  match q.val with
  | 0 => ⟨9073,17,19⟩
  | 1 => ⟨9396,19,17⟩
  | 2 => ⟨9887,5,19⟩
  | 3 => ⟨9982,19,5⟩
  | 4 => ⟨10077,5,19⟩
  | 5 => ⟨10172,19,5⟩
  | 6 => ⟨10267,5,19⟩
  | 7 => ⟨10362,19,5⟩
  | 8 => ⟨10457,5,19⟩
  | _ => ⟨10552,19,5⟩

def archivedGridEnd (q : Fin 10) : ℕ :=
  (archivedGrid q).base + (archivedGrid q).rows * (archivedGrid q).cols

def occupiesArchiveGrid (q : Fin 10) (i : ℕ) : Prop :=
  (archivedGrid q).base ≤ i ∧ i < archivedGridEnd q

theorem archivedGridDisjoint : ∀ i j : Fin 10, i≠j →
    (archivedGridEnd i ≤ (archivedGrid j).base ∨ archivedGridEnd j ≤ (archivedGrid i).base) := by decide

theorem archivedGridAvoidsInputs : ∀ q : Fin 10,
    9072 < (archivedGrid q).base ∧ (archivedGridEnd q ≤9719 ∨ 9886 < (archivedGrid q).base) := by decide

theorem archivedGridRows : ∀ q : Fin 10, 2≤(archivedGrid q).rows := by decide

theorem occupiesArchiveGrid_unique {p q : Fin 10} {i : ℕ}
    (a : occupiesArchiveGrid p i) (b : occupiesArchiveGrid q i) : p=q := by
  by_contra ne
  have e := archivedGridDisjoint p q ne
  unfold occupiesArchiveGrid at a b
  omega

noncomputable def installArchivedCounters (states : Fin 10 → ℕ → ℕ → Bool)
    (v : ℕ → Bool) (i : ℕ) : Bool := by
  classical
  exact if h : ∃ q : Fin 10, occupiesArchiveGrid q i then
    let q := Classical.choose h
    stateAtSequentialSlot (archivedGrid q).cols (states q) (i-(archivedGrid q).base)
  else v i

theorem installArchivedCounters_preserves_inputs (states : Fin 10 → ℕ → ℕ → Bool)
    (v : ℕ → Bool) (i : ℕ) (hi : i≤9072 ∨ (9719≤i ∧ i≤9886)) :
    installArchivedCounters states v i = v i := by
  have H : ¬∃ q : Fin 10, occupiesArchiveGrid q i := by
    rintro ⟨q,h⟩
    have ht := archivedGridAvoidsInputs q
    unfold occupiesArchiveGrid at h
    omega
  simp [installArchivedCounters,H]

theorem installArchivedCounters_reads (states : Fin 10 → ℕ → ℕ → Bool)
    (v : ℕ → Bool) (q : Fin 10) (r j : ℕ)
    (hr : r<(archivedGrid q).rows) (hj : j<(archivedGrid q).cols) :
    numericCounterState (installArchivedCounters states v) (archivedGrid q).base
      (archivedGrid q).cols r j = states q r j := by
  let i := numericStateNumber (archivedGrid q).base (archivedGrid q).cols r j
  have hs := sequentialSlot_inRange (archivedGrid q).rows (archivedGrid q).cols r j
    (archivedGridRows q) hr hj
  have ow : occupiesArchiveGrid q i := by
    unfold occupiesArchiveGrid archivedGridEnd
    dsimp [i,numericStateNumber]
    omega
  have he : ∃ k : Fin 10, occupiesArchiveGrid k i := ⟨q,ow⟩
  have kEq := occupiesArchiveGrid_unique (Classical.choose_spec he) ow
  change installArchivedCounters states v i = states q r j
  unfold installArchivedCounters
  rw [dif_pos he,kEq]
  dsimp [i,numericStateNumber]
  rw [Nat.add_sub_cancel_left]
  exact stateAtSequentialSlot_correct _ _ _ hj _

private def excessZeroKey (g : Coord) : Fin 10 :=
  ⟨2+2*g.val,by have := g.isLt; omega⟩

private def excessOneKey (g : Coord) : Fin 10 :=
  ⟨3+2*g.val,by have := g.isLt; omega⟩

private theorem excessZeroSpec (g : Coord) :
    archivedGrid (excessZeroKey g) = ⟨9887+190*g.val,5,19⟩ := by fin_cases g <;> rfl

private theorem excessOneSpec (g : Coord) :
    archivedGrid (excessOneKey g) = ⟨9982+190*g.val,19,5⟩ := by fin_cases g <;> rfl

private def gridWitnesses (zP sP : ℕ → ℕ → Bool) (zE sE : Coord → ℕ → ℕ → Bool)
    (q : Fin 10) : ℕ → ℕ → Bool :=
  match q.val with
  | 0 => zP | 1 => sP
  | 2 => zE 0 | 3 => sE 0
  | 4 => zE 1 | 5 => sE 1
  | 6 => zE 2 | 7 => sE 2
  | 8 => zE 3 | _ => sE 3

private theorem witnessesZero (zP sP : ℕ → ℕ → Bool) (zE sE : Coord → ℕ → ℕ → Bool)
    (g : Coord) : gridWitnesses zP sP zE sE (excessZeroKey g) = zE g := by fin_cases g <;> rfl

private theorem witnessesOne (zP sP : ℕ → ℕ → Bool) (zE sE : Coord → ℕ → ℕ → Bool)
    (g : Coord) : gridWitnesses zP sP zE sE (excessOneKey g) = sE g := by fin_cases g <;> rfl

/-- A linear size-17 design with degree minimum two has a single
numbered assignment that satisfies every exact-count block simultaneously
and leaves all original word, pair and degree inputs unchanged. -/
theorem geometry_satisfies_archived_cardinality (D : Design 6) (linear : Linear D)
    (size : D.card=17) (minimum : ∀ g : Coord, ∀ a : Fin 6, 2≤freq D (g,a))
    (v : ℕ → Bool)
    (hpair : ∀ p : PairKey 6, v (pairNumber p) = (encode D).pair p)
    (hdeg : ∀ g : Coord, ∀ a : Fin 6, ∀ d : Fin 7,
      v (degreeThresholdNumber g a d) = decide (d.val≤freq D (g,a))) :
    ∃ w : ℕ → Bool,
      (∀ i, i≤9072 ∨ (9719≤i ∧ i≤9886) → w i=v i) ∧
      (∀ c ∈ archiveProjectionCountBlock, NumberedHolds w c) ∧
      ∀ g : Coord, ∀ c ∈ archiveDegreeExcessCountBlock g, NumberedHolds w c := by
  obtain ⟨⟨zp,sp,hzp,hsp⟩,hex⟩ := geometry_seventeen_counter_states D linear size minimum v hpair hdeg
  choose ze se he using hex
  let states := gridWitnesses zp sp ze se
  let w := installArchivedCounters states v
  have keep (i : ℕ) (hi : i≤9072 ∨ (9719≤i ∧ i≤9886)) : w i = v i :=
    installArchivedCounters_preserves_inputs states v i hi
  have inputP (i : ℕ) (hi : i<36) : w (projectionCounterId i)=v (projectionCounterId i) := by
    apply keep
    left
    dsimp [projectionCounterId]
    omega
  have inpPosP (i : ℕ) : 0<projectionCounterId i := by
    dsimp [projectionCounterId]
    omega
  have inputE (g : Coord) (i : ℕ) : w (degreeExcessCounterId g i) = v (degreeExcessCounterId g i) := by
    apply keep
    right
    exact degreeThresholdNumber_bounds _ _ _
  have inpPosE (g : Coord) (i : ℕ) : 0<degreeExcessCounterId g i := by
    have b : 9719 ≤ degreeExcessCounterId g i := (degreeThresholdNumber_bounds _ _ _).1
    omega
  refine ⟨w,keep,?_,?_⟩
  · intro c hc
    rcases List.mem_append.mp hc with mz | ms
    · refine numericSequentialBlock_holds 17 19 9073 projectionCounterId false w (by decide)
        (fun i _ => inpPosP i) ?_ c mz
      refine sequentialBound_of_local_agreement 17 19 (by decide) _ _ _ _ ?_ ?_ hzp
      · intro i hi
        exact congrArg (fun b : Bool => !b) (inputP i hi).symm
      · intro r hr j hj
        symm
        exact installArchivedCounters_reads states v 0 r j hr hj
    · refine numericSequentialBlock_holds 19 17 9396 projectionCounterId true w (by decide)
        (fun i _ => inpPosP i) ?_ c ms
      refine sequentialBound_of_local_agreement 19 17 (by decide) _ _ _ _ ?_ ?_ hsp
      · intro i hi
        exact (inputP i hi).symm
      · intro r hr j hj
        symm
        exact installArchivedCounters_reads states v 1 r j hr hj
  · intro g c hc
    rcases List.mem_append.mp hc with mz | ms
    · refine numericSequentialBlock_holds 5 19 (9887+190*g.val) (degreeExcessCounterId g) false w
        (by omega) (fun i _ => inpPosE g i) ?_ c mz
      refine sequentialBound_of_local_agreement 5 19 (by decide) _ _ _ _ ?_ ?_ (he g).1
      · intro i hi
        exact congrArg (fun b : Bool => !b) (inputE g i).symm
      · intro r hr j hj
        symm
        have re := installArchivedCounters_reads states v (excessZeroKey g) r j
          (by simpa [excessZeroSpec] using hr) (by simpa [excessZeroSpec] using hj)
        rw [excessZeroSpec] at re
        exact re.trans (congrFun (congrFun (witnessesZero zp sp ze se g) r) j)
    · refine numericSequentialBlock_holds 19 5 (9982+190*g.val) (degreeExcessCounterId g) true w
        (by omega) (fun i _ => inpPosE g i) ?_ c ms
      refine sequentialBound_of_local_agreement 19 5 (by decide) _ _ _ _ ?_ ?_ (he g).2
      · intro i hi
        exact (inputE g i).symm
      · intro r hr j hj
        symm
        have re := installArchivedCounters_reads states v (excessOneKey g) r j
          (by simpa [excessOneSpec] using hr) (by simpa [excessOneSpec] using hj)
        rw [excessOneSpec] at re
        exact re.trans (congrFun (congrFun (witnessesOne zp sp ze se g) r) j)

#print axioms installArchivedCounters_reads
#print axioms geometry_satisfies_archived_cardinality

end LatinGap.PairEncoding

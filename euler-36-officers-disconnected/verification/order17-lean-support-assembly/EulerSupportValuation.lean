import EulerSupportWords
import EulerNumberedCounters

namespace LatinGap.PairEncoding

def supportCounterBase (p : PairKey 6) : ℕ := 1513 + 35*(pairNumber p-1297)

theorem supportCounterBase_bounds (p : PairKey 6) :
    1513 ≤ supportCounterBase p ∧ supportCounterBase p+35 ≤9073 := by
  have h := pairNumber_bounds p
  unfold supportCounterBase
  omega

def supportGridOwns (p : PairKey 6) (idx : ℕ) : Prop :=
  supportCounterBase p≤idx ∧ idx<supportCounterBase p+35

theorem supportGridOwner_unique {p q : PairKey 6} {idx : ℕ}
    (hp : supportGridOwns p idx) (hq : supportGridOwns q idx) : p=q := by
  apply pairNumber_injective
  have h₁ := pairNumber_bounds p
  have h₂ := pairNumber_bounds q
  unfold supportGridOwns supportCounterBase at hp hq
  omega

noncomputable def installSupportGrids (v : ℕ → Bool) (s : PairKey 6 → ℕ → ℕ → Bool)
    (i : ℕ) : Bool := by
  classical
  exact if h : ∃ p : PairKey 6, supportGridOwns p i then
    let p := Classical.choose h
    s p (i-supportCounterBase p) 0
  else v i

theorem installSupportGrids_preserves (v : ℕ → Bool) (s : PairKey 6 → ℕ → ℕ → Bool)
    (i : ℕ) (hi : i≤1512 ∨ 9073≤i) : installSupportGrids v s i = v i := by
  have e : ¬∃ p : PairKey 6, supportGridOwns p i := by
    rintro ⟨p,hp⟩
    have b := supportCounterBase_bounds p
    unfold supportGridOwns at hp
    omega
  simp [installSupportGrids,e]

theorem installSupportGrids_reads (v : ℕ → Bool) (s : PairKey 6 → ℕ → ℕ → Bool)
    (p : PairKey 6) (r j : ℕ) (hr : r<35) (hj : j<1) :
    numericCounterState (installSupportGrids v s) (supportCounterBase p) 1 r j = s p r j := by
  have zero : j=0 := by omega
  subst j
  have slot : sequentialSlot 1 r 0 = r := by
    by_cases h : r<2 <;> simp [sequentialSlot,h]
  unfold numericCounterState numericStateNumber
  rw [slot]
  let i := supportCounterBase p+r
  have gp : supportGridOwns p i := by
    unfold supportGridOwns
    dsimp [i]
    omega
  have ex : ∃ q : PairKey 6, supportGridOwns q i := ⟨p,gp⟩
  have owner := supportGridOwner_unique (Classical.choose_spec ex) gp
  change installSupportGrids v s i = _
  unfold installSupportGrids
  rw [dif_pos ex,owner]
  simp [i]

def supportBackNumberedClause (p : PairKey 6) : List ℤ :=
  literal (pairNumber p) false ::
    ((List.range 36).map (fun i => literal (supportWordInputId p i) true))

def supportForwardNumberedClause (p : PairKey 6) (i : ℕ) : List ℤ :=
  [literal (supportWordInputId p i) false, literal (pairNumber p) true]

/-- Complete archived local support block: back implication, all forward
word implications, then the 35-state at-most-one counter. -/
def archiveSupportBlock (p : PairKey 6) : List (List ℤ) :=
  supportBackNumberedClause p ::
    ((List.range 36).map (supportForwardNumberedClause p) ++
      numericSequentialBlock 35 1 (supportCounterBase p) (supportWordInputId p) true)

theorem supportForwardNumberedClause_holds (D : Design 6) (v : ℕ → Bool)
    (hword : ∀ w : Word 6, v (wordNumber w) = (encode D).select w)
    (hpair : ∀ p : PairKey 6, v (pairNumber p) = (encode D).pair p)
    (p : PairKey 6) (i : ℕ) :
    NumberedHolds v (supportForwardNumberedClause p i) := by
  let t : Fin 36 := ⟨i%36,by omega⟩
  let w := supportWord p t
  change NumberedHolds v [literal (wordNumber w) false,literal (pairNumber p) true]
  by_cases h : v (wordNumber w)=true
  · have hw : w∈D := (select_encode D w).mp ((hword w).symm.trans h)
    have matchW := supportWord_matches p t
    have u : Used D (p.i,p.a) (p.j,p.b) := ⟨ne_of_lt p.increasing,w,hw,matchW.1,matchW.2⟩
    have hp := (hpair p).trans ((pair_encode D p).mpr u)
    exact holds_literal_of_mem (by simp) (by have := (pairNumber_bounds p).1; omega) hp
  · have hf : v (wordNumber w)=false := by
      cases E : v (wordNumber w) <;> simp_all
    exact holds_literal_of_mem (by simp) (wordNumber_bounds w).1 hf

theorem supportBackNumberedClause_holds (D : Design 6) (v : ℕ → Bool)
    (hword : ∀ w : Word 6, v (wordNumber w) = (encode D).select w)
    (hpair : ∀ p : PairKey 6, v (pairNumber p) = (encode D).pair p)
    (p : PairKey 6) : NumberedHolds v (supportBackNumberedClause p) := by
  by_cases h : v (pairNumber p)=true
  · have u := (pair_encode D p).mp ((hpair p).symm.trans h)
    obtain ⟨_,w,hw,hm₁,hm₂⟩ := u
    obtain ⟨t,ht⟩ := supportWord_onto p w ⟨hm₁,hm₂⟩
    have hid : supportWordInputId p t.val=wordNumber w :=
      (supportWordInputId_fin p t).trans (congrArg wordNumber ht)
    have vtrue : v (supportWordInputId p t.val)=true := by
      rw [hid,hword]
      exact (select_encode D w).mpr hw
    have memb : literal (supportWordInputId p t.val) true∈supportBackNumberedClause p := by
      unfold supportBackNumberedClause
      exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨t.val,List.mem_range.mpr t.isLt,rfl⟩)
    exact holds_literal_of_mem memb (by rw [hid]; exact (wordNumber_bounds w).1) vtrue
  · have hf : v (pairNumber p)=false := by cases E : v (pairNumber p) <;> simp_all
    exact holds_literal_of_mem (by simp [supportBackNumberedClause])
      (by have := (pairNumber_bounds p).1; omega) hf

/-- The 216 disjoint physical support counters can be installed
simultaneously, preserving all original word/pair bits and every
other auxiliary block (including the exact-count blocks). -/
theorem geometry_satisfies_archived_support_blocks (D : Design 6) (linear : Linear D)
    (v : ℕ → Bool)
    (hword : ∀ w : Word 6, v (wordNumber w) = (encode D).select w)
    (hpair : ∀ p : PairKey 6, v (pairNumber p) = (encode D).pair p) :
    ∃ w : ℕ → Bool,
      (∀ i, i≤1512 ∨ 9073≤i → w i=v i) ∧
      ∀ p : PairKey 6, ∀ c∈archiveSupportBlock p, NumberedHolds w c := by
  have possible (p : PairKey 6) :
      ∃ s, SequentialBound 35 1 (fun i => v (supportWordInputId p i)) s :=
    (sequentialBound_iff 35 1 (by decide) _).mpr (geometry_support_prefixOnes D linear v hword p)
  choose s hs using possible
  let w := installSupportGrids v s
  have keep (i : ℕ) (hi : i≤1512 ∨ 9073≤i) : w i = v i :=
    installSupportGrids_preserves v s i hi
  have hw (u : Word 6) : w (wordNumber u) = (encode D).select u :=
    (keep _ (Or.inl (by have := (wordNumber_bounds u).2; omega))).trans (hword u)
  have hp (p : PairKey 6) : w (pairNumber p) = (encode D).pair p :=
    (keep _ (Or.inl (pairNumber_bounds p).2)).trans (hpair p)
  refine ⟨w,keep,?_⟩
  intro p c hc
  rcases List.mem_cons.mp hc with e | rest
  · rw [e]
    exact supportBackNumberedClause_holds D w hw hp p
  · rcases List.mem_append.mp rest with forward | amo
    · obtain ⟨i,_,e⟩ := List.mem_map.mp forward
      rw [← e]
      exact supportForwardNumberedClause_holds D w hw hp p i
    · have nPos : 0 < supportCounterBase p := by have := (supportCounterBase_bounds p).1; omega
      have wp (i : ℕ) : 0<supportWordInputId p i ∧ supportWordInputId p i≤1296 :=
        wordNumber_bounds _
      apply numericSequentialBlock_holds 35 1 (supportCounterBase p) (supportWordInputId p)
        true w nPos (fun i _ => (wp i).1) _ c amo
      refine sequentialBound_of_local_agreement 35 1 (by decide) _ _ _ _ ?_ ?_ (hs p)
      · intro i hi
        exact (keep _ (Or.inl (by have := (wp i).2; omega))).symm
      · intro r hr j hj
        exact (installSupportGrids_reads v s p r j hr hj).symm

#print axioms installSupportGrids_reads
#print axioms geometry_satisfies_archived_support_blocks

end LatinGap.PairEncoding

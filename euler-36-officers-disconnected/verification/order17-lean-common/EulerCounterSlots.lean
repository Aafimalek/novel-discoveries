import EulerSequentialCount

namespace LatinGap.PairEncoding

/-- PySAT allocates the first two state rows in alternating order on its
first pass; all later rows are allocated consecutively. -/
def sequentialSlot (cols r j : ℕ) : ℕ :=
  if r<2 then 2*j+r else cols*r+j

def stateAtSequentialSlot (cols : ℕ) (s : ℕ → ℕ → Bool) (offset : ℕ) : Bool :=
  if offset<2*cols then s (offset%2) (offset/2) else s (offset/cols) (offset%cols)

theorem stateAtSequentialSlot_correct (cols r j : ℕ) (hj : j<cols) (s : ℕ → ℕ → Bool) :
    stateAtSequentialSlot cols s (sequentialSlot cols r j) = s r j := by
  by_cases h : r<2
  · have hh : 2*j+r<2*cols := by omega
    have hr : (2*j+r)%2=r := by omega
    have hd : (2*j+r)/2=j := by omega
    simp [sequentialSlot,stateAtSequentialSlot,h,hh,hr,hd]
  · have hb : 2*cols≤cols*r := by
      have H := Nat.mul_le_mul_left cols (show 2≤r by omega)
      simpa [Nat.mul_comm] using H
    have hh : ¬cols*r+j<2*cols := by omega
    have hpos : 0<cols := by omega
    have hd : (cols*r+j)/cols=r := by
      rw [Nat.add_comm, Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hj, Nat.zero_add]
    have hm : (cols*r+j)%cols=j := by
      rw [Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hj]
    simp [sequentialSlot,stateAtSequentialSlot,h,hh,hd,hm]

theorem sequentialSlot_inRange (rows cols r j : ℕ) (hm : 2≤rows) (hr : r<rows) (hj : j<cols) :
    sequentialSlot cols r j < rows*cols := by
  by_cases h : r<2
  · have hm' := Nat.mul_le_mul_right cols hm
    simp [sequentialSlot,h]
    omega
  · have hnext := Nat.mul_le_mul_left cols (show r+1≤rows by omega)
    have hle : cols*r+cols≤rows*cols := by
      rw [Nat.mul_add, Nat.mul_one] at hnext
      simpa only [Nat.mul_comm cols rows] using hnext
    simp [sequentialSlot,h]
    omega

/-- Overwrite exactly one rectangular auxiliary block. -/
def installSequentialGrid (base rows cols : ℕ) (s : ℕ → ℕ → Bool)
    (v : ℕ → Bool) (index : ℕ) : Bool :=
  if base ≤ index ∧ index < base+rows*cols then stateAtSequentialSlot cols s (index-base)
  else v index

theorem installSequentialGrid_outside (base rows cols : ℕ) (s : ℕ → ℕ → Bool)
    (v : ℕ → Bool) (index : ℕ) (outside : index<base ∨ base+rows*cols≤index) :
    installSequentialGrid base rows cols s v index = v index := by
  have t : ¬(base≤index ∧ index<base+rows*cols) := by omega
  simp [installSequentialGrid,t]

theorem installSequentialGrid_reads (base rows cols : ℕ) (s : ℕ → ℕ → Bool)
    (v : ℕ → Bool) (r j : ℕ) (hm : 2≤rows) (hr : r<rows) (hj : j<cols) :
    installSequentialGrid base rows cols s v (base+sequentialSlot cols r j) = s r j := by
  have slot := sequentialSlot_inRange rows cols r j hm hr hj
  have t : base≤base+sequentialSlot cols r j ∧ base+sequentialSlot cols r j<base+rows*cols :=
    ⟨by omega,by omega⟩
  simp [installSequentialGrid, t, stateAtSequentialSlot_correct cols r j hj]

/-- Rewrite bounded state variables and the bounded input numbers in the
semantic sequential-grid specification. -/
theorem sequentialBound_of_local_agreement (m k : ℕ) (hk : 0<k)
    (x y : ℕ → Bool) (s t : ℕ → ℕ → Bool)
    (hx : ∀ i<m+k, x i = y i) (hs : ∀ r<m, ∀ j<k, s r j=t r j)
    (h : SequentialBound m k x s) : SequentialBound m k y t := by
  rcases h with ⟨initial,horizontal,diagonal,final⟩
  refine ⟨?_,?_,?_,?_⟩
  · intro r hr hy
    rw [← hs r hr 0 hk]
    exact initial r hr ((hx r (by omega)).trans hy)
  · intro r j hr hj hit
    rw [← hs (r+1) hr j hj]
    exact horizontal r j hr hj ((hs r (by omega) j hj).trans hit)
  · intro r j hr hj hit hy
    rw [← hs r hr (j+1) hj]
    exact diagonal r j hr hj ((hs r hr j (by omega)).trans hit)
      ((hx (r+j+1) (by omega)).trans hy)
  · intro r hr hit
    rw [← hx (r+k) (by omega)]
    exact final r hr ((hs r hr (k-1) (by omega)).trans hit)

#print axioms stateAtSequentialSlot_correct
#print axioms installSequentialGrid_reads
#print axioms sequentialBound_of_local_agreement

end LatinGap.PairEncoding

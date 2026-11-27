import EulerCounterSlots
import EulerDegreeThreshold
import EulerGeometryCounters

namespace LatinGap.PairEncoding

def numericStateNumber (base cols r j : ℕ) : ℕ :=
  base + sequentialSlot cols r j

def numericCounterState (v : ℕ → Bool) (base cols : ℕ) (r j : ℕ) : Bool :=
  v (numericStateNumber base cols r j)

def numericCounterInput (v : ℕ → Bool) (idx : ℕ → ℕ) (sign : Bool) (i : ℕ) : Bool :=
  if sign then v (idx i) else !(v (idx i))

/-- The archived minimum-cardinality and maximum-cardinality counters
use the same clause traversal after complementing their input signs. -/
def numericSequentialBlock (m k base : ℕ) (idx : ℕ → ℕ) (sign : Bool) : List (List ℤ) :=
  let l (i : ℕ) := literal (idx i) (!sign)
  let s (r j : ℕ) (sign' : Bool) := literal (numericStateNumber base k r j) sign'
  (List.range m).flatMap fun r =>
    [l r, s r 0 true] ::
      ((List.range k).flatMap fun j =>
        (if r+1<m then [[s r j false, s (r+1) j true]] else []) ++
        if j+1<k then [[l (r+j+1), s r j false, s r (j+1) true]]
        else [[l (r+k), s r j false]])

private theorem false_input_literal (v : ℕ → Bool) (idx : ℕ → ℕ) (sign : Bool)
    (i : ℕ) (h : ¬ numericCounterInput v idx sign i = true) :
    v (idx i) = !sign := by
  cases sign <;> cases e : v (idx i) <;> simp_all [numericCounterInput]

private theorem false_state_from_not_true (b : Bool) (h : ¬ b = true) : b = false := by
  cases b <;> simp_all

/-- The exact ordered clause list is satisfied by any valuation whose
input/state projections satisfy the already checked semantic grid. -/
theorem numericSequentialBlock_holds (m k base : ℕ) (idx : ℕ → ℕ) (sign : Bool)
    (v : ℕ → Bool) (basePos : 0<base)
    (inputPos : ∀ i<m+k, 0<idx i)
    (bound : SequentialBound m k (numericCounterInput v idx sign)
      (numericCounterState v base k)) :
    ∀ c ∈ numericSequentialBlock m k base idx sign, NumberedHolds v c := by
  let l (i : ℕ) := literal (idx i) (!sign)
  let n (r j : ℕ) := numericStateNumber base k r j
  let s (r j : ℕ) (b : Bool) := literal (n r j) b
  have np (r j : ℕ) : 0<n r j := by
    dsimp [n,numericStateNumber]
    omega
  intro c hc
  obtain ⟨r,hr,hR⟩ := List.mem_flatMap.mp hc
  have hrlt := List.mem_range.mp hr
  rcases List.mem_cons.mp hR with eq | more
  · subst c
    change NumberedHolds v [l r, s r 0 true]
    by_cases h : numericCounterInput v idx sign r = true
    · exact holds_literal_of_mem (by simp [s]) (np r 0) (bound.1 r hrlt h)
    · exact holds_literal_of_mem (by simp [l]) (inputPos r (by omega))
        (false_input_literal v idx sign r h)
  · obtain ⟨j,hj,hJ⟩ := List.mem_flatMap.mp more
    have hjlt := List.mem_range.mp hj
    rcases List.mem_append.mp hJ with hore | de
    · by_cases good : r+1<m
      · simp only [if_pos good,List.mem_singleton] at hore
        subst c
        change NumberedHolds v [s r j false, s (r+1) j true]
        by_cases hp : numericCounterState v base k r j = true
        · exact holds_literal_of_mem (by simp [s]) (np (r+1) j) (bound.2.1 r j good hjlt hp)
        · exact holds_literal_of_mem (by simp [s]) (np r j) (false_state_from_not_true _ hp)
      · simp [good] at hore
    · by_cases hj' : j+1<k
      · simp only [if_pos hj',List.mem_singleton] at de
        subst c
        change NumberedHolds v [l (r+j+1),s r j false,s r (j+1) true]
        by_cases h₁ : numericCounterState v base k r j = true
        · by_cases h₂ : numericCounterInput v idx sign (r+j+1) = true
          · exact holds_literal_of_mem (by simp [s]) (np r (j+1))
              (bound.2.2.1 r j hrlt hj' h₁ h₂)
          · exact holds_literal_of_mem (by simp [l]) (inputPos (r+j+1) (by omega))
              (false_input_literal v idx sign _ h₂)
        · exact holds_literal_of_mem (by simp [s]) (np r j) (false_state_from_not_true _ h₁)
      · simp only [if_neg hj',List.mem_singleton] at de
        subst c
        change NumberedHolds v [l (r+k),s r j false]
        by_cases h₁ : numericCounterState v base k r j = true
        · have eq : j=k-1 := by omega
          have stop := bound.2.2.2 r hrlt (by rwa [← eq])
          exact holds_literal_of_mem (by simp [l]) (inputPos (r+k) (by omega))
            (false_input_literal v idx sign _ (by rw [stop]; decide))
        · exact holds_literal_of_mem (by simp [s]) (np r j) (false_state_from_not_true _ h₁)

def projectionCounterId (i : ℕ) : ℕ := 1297+i

def degreeExcessCounterId (g : Coord) (i : ℕ) : ℕ :=
  degreeThresholdNumber g ⟨(i/4)%6, by omega⟩ ⟨3+i%4, by omega⟩

def archiveProjectionCountBlock : List (List ℤ) :=
  numericSequentialBlock 17 19 9073 projectionCounterId false ++
  numericSequentialBlock 19 17 9396 projectionCounterId true

def archiveDegreeExcessCountBlock (g : Coord) : List (List ℤ) :=
  numericSequentialBlock 5 19 (9887+190*g.val) (degreeExcessCounterId g) false ++
  numericSequentialBlock 19 5 (9982+190*g.val) (degreeExcessCounterId g) true

#print axioms numericSequentialBlock_holds

end LatinGap.PairEncoding

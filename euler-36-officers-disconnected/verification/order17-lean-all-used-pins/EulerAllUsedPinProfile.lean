import EulerActualDiagramRealization
import EulerAllUsedFrequencies
import EulerCommonCounterAssembly
import EulerGeometryValuation

namespace LatinGap.PairEncoding
open EulerAllUsedDiagrams

/-- Decode the archive's four decimal digits as a word of order six.
The extra modulo six makes this total; valid archived digits are ≤5. -/
def decimalWord (code : Nat) : Word 6 :=
  fun j => ⟨(code / 10^(3-j.val) % 10) % 6,by omega⟩

def decimalCode (w : Word 6) : Nat :=
  (List.ofFn fun j : Coord => (w j).val).foldl (fun a b => a*10+b) 0

@[simp] theorem decimalWord_decimalCode (w : Word 6) : decimalWord (decimalCode w) = w := by
  have h0 := (w 0).isLt
  have h1 := (w 1).isLt
  have h2 := (w 2).isLt
  have h3 := (w 3).isLt
  have hCode : decimalCode w = 1000*(w 0).val + 100*(w 1).val + 10*(w 2).val + (w 3).val := by
    simp only [decimalCode,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil, Nat.zero_mul,Nat.zero_add]
    change (((w 0).val*10+(w 1).val)*10+(w 2).val)*10+(w 3).val = _
    omega
  funext i
  apply Fin.ext
  rw [show (decimalWord (decimalCode w) i).val = (decimalCode w / 10^(3-i.val) % 10) % 6 from rfl,hCode]
  fin_cases i <;> norm_num <;> omega

theorem actualRowCodes_eq (W : Coord → Word 6) :
    actualRowCodes W = List.ofFn (fun i => decimalCode (W i)) := rfl

theorem actualRowCodes_present {D : Design 6} (W : Coord → Word 6)
    (hW : ∀ i, W i ∈ D) (code : ℕ) (hc : code ∈ actualRowCodes W) :
    decimalWord code ∈ D := by
  rw [actualRowCodes_eq,List.mem_ofFn] at hc
  obtain ⟨i,rfl⟩ := hc
  simpa using hW i

def archiveAllUsedAnchorUnits : List (List Int) :=
  [0,111].map (fun n => [literal (wordNumber (decimalWord n)) true])

def archiveAllUsedPinProfile (codes : List Nat) : List (List Int) :=
  (codes.map fun n => [literal (wordNumber (decimalWord n)) true]) ++
  ((List.ofFn fun g : Coord => g).flatMap fun g =>
    (List.ofFn fun a : Fin 6 =>
      [literal (degreeThresholdNumber g a 3) (decide (a ≠ 0))]))

/-- All low-low pairs in the normalized branch are supported by 0000.
The archived file uses the word pin and the common support clauses,
not these derived pair units separately. -/
def allUsedZeroPairUnits : List (List Int) :=
  archivedCoordPairs.map fun ij => [literal (pairNumber (candidatePair (fun _ => 0) ij)) true]

def wordUnit (w : Word 6) : List Int := [literal (wordNumber w) true]

theorem wordUnit_of_mem (D : Design 6) (v : ℕ → Bool)
    (hword : ∀ w : Word 6, v (wordNumber w) = (encode D).select w) {w : Word 6}
    (hw : w ∈ D) : NumberedHolds v (wordUnit w) := by
  apply holds_literal_of_mem (b := true) (by simp [wordUnit]) (wordNumber_bounds w).1
  exact (hword w).trans ((select_encode D w).mpr hw)

/-- Satisfy the actual 28-clause all-used pin/profile block, for any
numbered valuation having the correct word and degree bits. -/
theorem allUsed_archive_pin_profile_holds (D : Design 6) (v : ℕ → Bool)
    (hword : ∀ w : Word 6, v (wordNumber w) = (encode D).select w)
    (hdeg : ∀ (g : Coord) (a : Fin 6) (d : Fin 7),
      v (degreeThresholdNumber g a d) = decide (d.val ≤ freq D (g,a)))
    (W : Coord → Word 6) (hW : ∀ i, W i ∈ D)
    (hprofile : ∀ (g : Coord) (a : Fin 6), freq D (g,a) = if a=0 then 2 else 3)
    (c : List Int) (hc : c ∈ archiveAllUsedPinProfile (actualRowCodes W)) :
    NumberedHolds v c := by
  rcases List.mem_append.mp hc with h | h
  · obtain ⟨n,hn,rfl⟩ := List.mem_map.mp h
    exact wordUnit_of_mem D v hword (actualRowCodes_present W hW n hn)
  · obtain ⟨g,_,hg⟩ := List.mem_flatMap.mp h
    obtain ⟨a,rfl⟩ := List.mem_ofFn.mp hg
    apply holds_literal_of_mem (id := degreeThresholdNumber g a 3) (b := decide (a ≠ 0)) (by simp) (by
      have := (degreeThresholdNumber_bounds g a 3).1; omega)
    rw [hdeg,hprofile]
    by_cases hz : a=0 <;> simp [hz]

theorem published_has_first_anchor : ∀ d ∈ published, 111 ∈ d := by decide +kernel

theorem allUsed_archive_anchors_holds (D : Design 6) (v : ℕ → Bool)
    (hword : ∀ w : Word 6, v (wordNumber w) = (encode D).select w)
    (zero : (fun _ => 0) ∈ D)
    (W : Coord → Word 6) (hW : ∀ i, W i ∈ D) (hWpub : actualRowCodes W ∈ published)
    (c : List Int) (hc : c ∈ archiveAllUsedAnchorUnits) : NumberedHolds v c := by
  obtain ⟨n,hn,rfl⟩ := List.mem_map.mp hc
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hn
  rcases hn with rfl | rfl
  · have eq : decimalWord 0 = fun _ => 0 := by funext j; fin_cases j <;> decide
    exact wordUnit_of_mem D v hword (eq.symm ▸ zero)
  · exact wordUnit_of_mem D v hword
      (actualRowCodes_present W hW 111 (published_has_first_anchor _ hWpub))

theorem allUsed_zero_pair_holds (D : Design 6) (v : ℕ → Bool)
    (hpair : ∀ p : PairKey 6, v (pairNumber p) = (encode D).pair p)
    (zero : (fun _ => 0) ∈ D)
    (c : List Int) (hc : c ∈ allUsedZeroPairUnits) : NumberedHolds v c := by
  obtain ⟨ij,_,rfl⟩ := List.mem_map.mp hc
  let p := candidatePair (fun _ => 0 : Word 6) ij
  have hp : Used D (p.i,p.a) (p.j,p.b) := ⟨ne_of_lt p.increasing,_,zero,rfl,rfl⟩
  exact holds_literal_of_mem (b := true) (by simp [p])
    (by have := (pairNumber_bounds p).1; omega)
    ((hpair p).trans ((pair_encode D p).mpr hp))

/-- Derive the exact profile from the geometric all-used condition, in
coordinates where the central low has already been named zero. -/
theorem actual_allUsed_profile {D : Design 6} (hD : Linear D) (hsize : D.card=17)
    (hm : ∀ x : Label 6, 2 ≤ freq D x)
    (hall : ∀ (i j : Coord) (a b : Fin 6), i ≠ j →
      freq D (i,a)=2 → freq D (j,b)=2 → Used D (i,a) (j,b))
    (hzero : ∀ g : Coord, freq D (g,0)=2)
    (g : Coord) (a : Fin 6) :
    freq D (g,a) = if a=0 then 2 else 3 := by
  obtain ⟨low,hl,other⟩ := all_used_profile hD hsize hm hall g
  have eq : low = 0 := by
    by_contra ne
    have bad := (other 0 (fun e => ne e.symm)).symm.trans (hzero g)
    exact (by decide : 3 ≠ 2) bad
  subst low
  by_cases hz : a=0
  · simpa [hz] using hzero g
  · simpa [hz] using other a hz

#print axioms decimalWord_decimalCode
#print axioms allUsed_archive_pin_profile_holds
#print axioms allUsed_archive_anchors_holds
#print axioms allUsed_zero_pair_holds
#print axioms actual_allUsed_profile
end LatinGap.PairEncoding

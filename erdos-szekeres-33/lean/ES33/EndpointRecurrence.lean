import ES33.EndpointPacket

namespace ES33.Endpoint

abbrev Signs (n : ℕ) := Fin n → Fin n → Fin n → Bool

/-- An increasing selection; only its first `len` entries are used. -/
structure IsChain {n : ℕ} (χ : Signs n) (color : Bool) (len : ℕ)
    (f : ℕ → Fin n) : Prop where
  increasing : ∀ i j, i < j → j < len → f i < f j
  consecutive : ∀ i, i+2 < len → χ (f i) (f (i+1)) (f (i+2)) = color

def EndState {n : ℕ} (χ : Signs n) (color : Bool) (len : ℕ) (a b c : Fin n) : Prop :=
  ∃ f, IsChain χ color len f ∧ f 0 = a ∧ f (len-2) = b ∧ f (len-1) = c

def StartState {n : ℕ} (χ : Signs n) (color : Bool) (len : ℕ) (a b c : Fin n) : Prop :=
  ∃ f, IsChain χ color len f ∧ f 0 = a ∧ f 1 = b ∧ f (len-1) = c

def Ends {n : ℕ} (χ : Signs n) (color : Bool) (len : ℕ) (a c : Fin n) : Prop :=
  ∃ f, IsChain χ color len f ∧ f 0 = a ∧ f (len-1) = c

private theorem chain_three {n : ℕ} (χ : Signs n) {v : Bool} {a b c : Fin n}
    (hab : a < b) (hbc : b < c) (h : χ a b c = v) :
    ∃ f, IsChain χ v 3 f ∧ f 0 = a ∧ f 1 = b ∧ f 2 = c := by
  refine ⟨fun i => if i=0 then a else if i=1 then b else c, ⟨?_,?_⟩,
    by simp, by simp, by simp⟩
  · intro i j hij hj
    have hj' : j=1 ∨ j=2 := by omega
    rcases hj' with rfl|rfl
    · have hi' : i=0 := by omega
      simpa [hi'] using hab
    · have hi' : i=0 ∨ i=1 := by omega
      rcases hi' with rfl|rfl
      · simpa using hab.trans hbc
      · simpa using hbc
  · intro i hi
    have hi' : i=0 := by omega
    simp [hi',h]

private theorem chain_three_sign {n : ℕ} (χ : Signs n) {v : Bool} {f : ℕ → Fin n}
    (hf : IsChain χ v 3 f) (a b c : Fin n) (h0 : f 0 = a) (h1 : f 1 = b) (h2 : f 2 = c) :
    a < b ∧ b < c ∧ χ a b c = v := by
  subst a
  subst b
  subst c
  exact ⟨hf.increasing 0 1 (by decide) (by decide),
    hf.increasing 1 2 (by decide) (by decide),
    hf.consecutive 0 (by decide)⟩

theorem end_base {n : ℕ} (χ : Signs n) (v : Bool) (a b c : Fin n) :
    EndState χ v 3 a b c ↔ a < b ∧ b < c ∧ χ a b c = v := by
  constructor
  · rintro ⟨f,hf,h0,h1,h2⟩
    exact chain_three_sign χ hf a b c h0 h1 h2
  · rintro ⟨hab,hbc,h⟩
    exact chain_three χ hab hbc h

theorem start_base {n : ℕ} (χ : Signs n) (v : Bool) (a b c : Fin n) :
    StartState χ v 3 a b c ↔ a < b ∧ b < c ∧ χ a b c = v := by
  exact end_base χ v a b c

/-- Recurrence used for a cap: append a point and keep the first point
and the last two points in the state. -/
theorem end_succ {n d : ℕ} (χ : Signs n) (v : Bool) (a b c : Fin n) (hd : 3 ≤ d) :
    EndState χ v (d+1) a b c ↔
      ∃ x, EndState χ v d a x b ∧ b < c ∧ χ x b c = v := by
  constructor
  · rintro ⟨f,hf,h0,hb,hc⟩
    have hb' : f (d-1) = b := by simpa only [show d+1-2=d-1 by omega] using hb
    have hc' : f d = c := by simpa only [show d+1-1=d by omega] using hc
    refine ⟨f (d-2), ⟨f,⟨?_,?_⟩,h0,rfl,hb'⟩, ?_,?_⟩
    · exact fun i j hij hj => hf.increasing i j hij (by omega)
    · exact fun i hi => hf.consecutive i (by omega)
    · rw [← hb',← hc']
      exact hf.increasing _ _ (by omega) (by omega)
    · have H := hf.consecutive (d-2) (by omega)
      rwa [show d-2+1=d-1 by omega,show d-2+2=d by omega,hb',hc'] at H
  · rintro ⟨x,⟨f,hf,h0,hx,hb⟩,hbc,hcol⟩
    let g : ℕ → Fin n := fun i => if i=d then c else f i
    refine ⟨g,⟨?_,?_⟩,?_,?_,?_⟩
    · intro i j hij hj
      by_cases hj' : j=d
      · subst j
        have hid : i ≠ d := by omega
        have hilast : f i ≤ f (d-1) := by
          rcases lt_or_eq_of_le (show i ≤ d-1 by omega) with h|h
          · exact (hf.increasing i (d-1) h (by omega)).le
          · rw [h]
        simpa [g,hid] using (le_trans hilast (le_of_eq hb)).trans_lt hbc
      · have hid : i ≠ d := by omega
        simp only [g,ite_eq_right hid,ite_eq_right hj']
        exact hf.increasing i j hij (by omega)
    · intro i hi
      by_cases hi' : i+2=d
      · have hid : i ≠ d := by omega
        have his : i+1 ≠ d := by omega
        simp only [g,ite_eq_right hid,ite_eq_right his,ite_eq_left hi']
        rwa [show i=d-2 by omega, show d-2+1=d-1 by omega,hx,hb]
      · have hid : i ≠ d := by omega
        have his : i+1 ≠ d := by omega
        simp only [g,ite_eq_right hid,ite_eq_right his,ite_eq_right hi']
        exact hf.consecutive i (by omega)
    · simpa [g,show 0≠d by omega] using h0
    · simp only [g,show d+1-2=d-1 by omega,ite_eq_right (show d-1≠d by omega),hb]
    · simp [g]

/-- Recurrence used for a cup: prepend a point and keep the first two
points and the last point in the state. -/
theorem start_succ {n d : ℕ} (χ : Signs n) (v : Bool) (a b c : Fin n) (hd : 3 ≤ d) :
    StartState χ v (d+1) a b c ↔
      ∃ x, StartState χ v d b x c ∧ a < b ∧ χ a b x = v := by
  constructor
  · rintro ⟨f,hf,ha,hb,hc⟩
    let g : ℕ → Fin n := fun j => f (j+1)
    refine ⟨f 2,⟨g,⟨?_,?_⟩,hb,rfl,?_⟩,?_,?_⟩
    · exact fun i j h hj => hf.increasing (i+1) (j+1) (by omega) (by omega)
    · intro i hi
      change χ (f (i+1)) (f (i+1+1)) (f (i+2+1)) = v
      exact hf.consecutive (i+1) (by omega)
    · simpa [g,show d-1+1=d by omega] using hc
    · rw [← ha,← hb]
      exact hf.increasing 0 1 (by decide) (by omega)
    · rw [← ha,← hb]
      exact hf.consecutive 0 (by omega)
  · rintro ⟨x,⟨f,hf,hb,hx,hc⟩,hab,hcol⟩
    let g : ℕ → Fin n := fun i => if i=0 then a else f (i-1)
    refine ⟨g,⟨?_,?_⟩,by simp [g],by simp [g,hb],?_⟩
    · intro i j hij hj
      have hj0 : j≠0 := by omega
      by_cases hi0 : i=0
      · subst i
        simp only [g,ite_eq_left rfl,ite_eq_right hj0]
        rw [← hb] at hab
        apply hab.trans_le
        rcases eq_or_lt_of_le (Nat.zero_le (j-1)) with h|h
        · rw [← h]
        · exact (hf.increasing 0 (j-1) h (by omega)).le
      · simp only [g,ite_eq_right hi0,ite_eq_right hj0]
        exact hf.increasing (i-1) (j-1) (by omega) (by omega)
    · intro i hi
      by_cases hi0 : i=0
      · subst i
        simpa [g,hb,hx] using hcol
      · simp only [g,ite_eq_right hi0,ite_eq_right (show i+1≠0 by omega),
          ite_eq_right (show i+2≠0 by omega)]
        rw [show i+1-1=(i-1)+1 by omega,show i+2-1=(i-1)+2 by omega]
        exact hf.consecutive (i-1) (by omega)
    · simp [g,show d≠0 by omega,hc]

/-- The recursive state depth counts the number of steps after length 3. -/
def forward {n : ℕ} (χ : Signs n) (v : Bool) : ℕ → Fin n → Fin n → Fin n → Prop
  | 0,a,b,c => a < b ∧ b < c ∧ χ a b c = v
  | d+1,a,b,c => ∃ x, forward χ v d a x b ∧ b < c ∧ χ x b c = v

def backward {n : ℕ} (χ : Signs n) (v : Bool) : ℕ → Fin n → Fin n → Fin n → Prop
  | 0,a,b,c => a < b ∧ b < c ∧ χ a b c = v
  | d+1,a,b,c => ∃ x, backward χ v d b x c ∧ a < b ∧ χ a b x = v

theorem forward_exact {n : ℕ} (χ : Signs n) (v : Bool)
    (d : ℕ) (a b c : Fin n) :
    forward χ v d a b c ↔ EndState χ v (d+3) a b c := by
  induction d generalizing a b c with
  | zero => exact (end_base χ v a b c).symm
  | succ d ih =>
    rw [show d+1+3=d+3+1 by omega, end_succ χ v a b c (by omega), forward]
    simp only [ih]

theorem backward_exact {n : ℕ} (χ : Signs n) (v : Bool)
    (d : ℕ) (a b c : Fin n) :
    backward χ v d a b c ↔ StartState χ v (d+3) a b c := by
  induction d generalizing a b c with
  | zero => exact (start_base χ v a b c).symm
  | succ d ih =>
    rw [show d+1+3=d+3+1 by omega, start_succ χ v a b c (by omega), backward]
    simp only [ih]

theorem ends_iff_forward {n : ℕ} (χ : Signs n) (v : Bool) (d : ℕ) (a c : Fin n) :
    Ends χ v (d+3) a c ↔ ∃ b, forward χ v d a b c := by
  constructor
  · rintro ⟨f,hf,ha,hc⟩
    exact ⟨f (d+3-2),(forward_exact χ v d _ _ _).mpr ⟨f,hf,ha,rfl,hc⟩⟩
  · rintro ⟨b,h⟩
    obtain ⟨f,hf,ha,_,hc⟩ := (forward_exact χ v d _ _ _).mp h
    exact ⟨f,hf,ha,hc⟩

theorem ends_iff_backward {n : ℕ} (χ : Signs n) (v : Bool) (d : ℕ) (a c : Fin n) :
    Ends χ v (d+3) a c ↔ ∃ b, backward χ v d a b c := by
  constructor
  · rintro ⟨f,hf,ha,hc⟩
    exact ⟨f 1,(backward_exact χ v d _ _ _).mpr ⟨f,hf,ha,rfl,hc⟩⟩
  · rintro ⟨b,h⟩
    obtain ⟨f,hf,ha,_,hc⟩ := (backward_exact χ v d _ _ _).mp h
    exact ⟨f,hf,ha,hc⟩

theorem ends_two_iff {n : ℕ} (χ : Signs n) (v : Bool) (a c : Fin n) :
    Ends χ v 2 a c ↔ a < c := by
  constructor
  · rintro ⟨f,hf,ha,hc⟩
    rw [← ha,← hc]
    exact hf.increasing 0 1 (by decide) (by decide)
  · intro h
    refine ⟨fun i => if i=0 then a else c,⟨?_,?_⟩,by simp,by simp⟩
    · intro i j hij hj
      have hi : i=0 := by omega
      have hj' : j=1 := by omega
      simp [hi,hj',h]
    · intro i hi
      omega

theorem Ends.shorten {n d : ℕ} {χ : Signs n}
    (hχ : SignotopeConstraints n χ) {v : Bool} {a c : Fin n}
    (hd : 2 ≤ d) (h : Ends χ v (d+1) a c) : Ends χ v d a c := by
  obtain ⟨f,hf,ha,hc⟩ := h
  let jmp : ℕ → ℕ := fun j => if j=0 then 0 else j+1
  have jmp_lt {i j : ℕ} (h : i<j) : jmp i < jmp j := by
    dsimp only [jmp]
    split_ifs <;> omega
  have jmp_bound {i : ℕ} (h : i<d) : jmp i < d+1 := by
    unfold jmp
    split_ifs <;> omega
  have all := selected_chain_sign_of_consecutive χ hχ f (d+1) v hf.increasing hf.consecutive
  refine ⟨fun i => f (jmp i),⟨?_,?_⟩,by simpa [jmp] using ha,?_⟩
  · exact fun i j hij hj => hf.increasing _ _ (jmp_lt hij) (jmp_bound hj)
  · intro i hi
    exact all _ _ _ (jmp_lt (by omega)) (jmp_lt (by omega)) (jmp_bound hi)
  · simpa [jmp,show d-1≠0 by omega,show d-1+1=d by omega] using hc

/-- On a legal signotope, an increasing consecutive-color witness is
monochromatic on every selected triple. -/
theorem IsChain.all_signs {n d : ℕ} {χ : Signs n}
    (hχ : SignotopeConstraints n χ) {v : Bool} {f : ℕ → Fin n}
    (h : IsChain χ v d f) :
    ∀ i j k, i < j → j < k → k < d → χ (f i) (f j) (f k) = v :=
  selected_chain_sign_of_consecutive χ hχ f d v h.increasing h.consecutive

#print axioms ends_two_iff
#print axioms Ends.shorten
#print axioms IsChain.all_signs
#print axioms end_succ
#print axioms start_succ
#print axioms forward_exact
#print axioms backward_exact
#print axioms ends_iff_forward
#print axioms ends_iff_backward

end ES33.Endpoint

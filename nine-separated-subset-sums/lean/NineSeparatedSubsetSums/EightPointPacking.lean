import NineSeparatedSubsetSums.FourPointSymmetry

open scoped BigOperators

namespace NineSeparatedSubsetSums

/-- Total charge on the eight signed offsets with fixed weights 148,a,b. -/
def octCharge (a b : ℤ) (f : ℤ → ℤ) (c : ℤ) : ℤ :=
  blockCharge a f (c-b) + blockCharge a f (c+b)

theorem octCharge_square (a b c : ℤ) :
    octCharge a b (· ^ 2) c = 8 * (c^2+148^2+a^2+b^2) := by
  rw [octCharge, blockSquare_identity, blockSquare_identity]
  ring

theorem octCharge_neg (a b c : ℤ) (f : ℤ → ℤ) (hs : ∀ z, f (-z)=f z) :
    octCharge a b f (-c) = octCharge a b f c := by
  unfold octCharge
  rw [show -c-b= -(c+b) by ring, show -c+b= -(c-b) by ring,
    blockCharge_neg _ _ _ hs, blockCharge_neg _ _ _ hs, add_comm]

theorem octCharge_sum_lower (a b lam : ℤ) (charge : ℤ → ℤ) (centers : List ℤ)
    (each : ∀ c ∈ centers, lam ≤ octCharge a b charge c) :
    lam * (centers.length : ℤ) ≤ ((spread 148 (spread a (spread b centers))).map charge).sum := by
  induction centers with
  | nil => simp [spread]
  | cons c centers ih =>
    have ev := each c List.mem_cons_self
    have rest := ih (fun k hk => each k (List.mem_cons_of_mem _ hk))
    unfold octCharge blockCharge at ev
    simp only [spread, List.flatMap_cons, List.cons_append, List.nil_append,
      List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one] at *
    linarith

/-- Check a finite window of nonnegative anchors; symmetry and the
unpenalized second moment handle all other centers. -/
theorem octCharge_check_from_positive_window (a b lam p : ℤ) (penalty : ℤ → ℤ)
    (nonneg : ∀ z, 0 ≤ penalty z) (even : ∀ z, penalty (-z)=penalty z)
    (R : ℕ) (bound : lam ≤ 8*((R : ℤ)^2+148^2+a^2+b^2))
    (check : ∀ j : Fin R, ((j.val : ℤ)+a+b)%2=p →
      lam ≤ octCharge a b (fun z => z^2+penalty z) (j.val : ℤ))
    (c : ℤ) (par : (c+a+b)%2=p) :
    lam ≤ octCharge a b (fun z => z^2+penalty z) c := by
  have pos (d : ℤ) (hd : 0 ≤ d) (hp : (d+a+b)%2=p) :
      lam ≤ octCharge a b (fun z => z^2+penalty z) d := by
    by_cases h : d < (R : ℤ)
    · let j : Fin R := ⟨d.toNat, by omega⟩
      have e : (j.val : ℤ)=d := Int.toNat_of_nonneg hd
      exact e ▸ check j (by rwa [e])
    · have hs : (R : ℤ)^2≤d^2 := by
        have h' := mul_nonneg (show 0 ≤ d-(R : ℤ) by omega) (show 0 ≤ d+(R : ℤ) by omega)
        nlinarith only [h']
      have pure := octCharge_square a b d
      unfold octCharge blockCharge at pure ⊢
      linarith [nonneg (d-b-a-148),nonneg (d-b-a+148),
        nonneg (d-b+a-148),nonneg (d-b+a+148),
        nonneg (d+b-a-148),nonneg (d+b-a+148),
        nonneg (d+b+a-148),nonneg (d+b+a+148)]
  by_cases hc : 0≤c
  · exact pos c hc par
  · have hn := pos (-c) (by omega) (by omega : (-c+a+b)%2=p)
    have E := octCharge_neg a b c (fun z => z^2+penalty z) (by
      intro z
      simp [even z])
    rwa [E] at hn

structure EightPointCertificate (a b p target : ℤ) where
  lambda : ℤ
  penalty : ℤ → ℤ
  box : Finset ℤ
  positive : ∀ z, 0 ≤ penalty z
  support : ∀ z, z ∉ box → penalty z = 0
  anchor : ∀ z, (z+a+b)%2=p → lambda ≤ octCharge a b (fun x => x^2+penalty x) z
  strong : 512*(target-1) < 64*lambda - ∑ z ∈ box, penalty z

private theorem octCastSum (l : List ℕ) :
    (l.sum : ℤ) = (l.map Int.ofNat).sum := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.sum_cons, List.map_cons, Nat.cast_add, ih]
    rfl

private theorem octCastSublists (l : List ℕ) :
    (natSubsetSums l).map Int.ofNat = (l.map Int.ofNat).sublists.map List.sum := by
  simp only [natSubsetSums, List.sublists_map, List.map_map]
  congr 1
  funext s
  exact octCastSum s

/-- Eight-point certificates give a bound for the original integer
positional subset sums, with the three fixed weights 148,a,b. -/
theorem eightPointNatMomentLower (a b target : ℕ) (tail : List ℕ)
    (len : tail.length=6) (distinct : (natSubsetSums (148::a::b::tail)).Nodup)
    (cert : ∀ p : ℤ, p=0 ∨ p=1 → EightPointCertificate a b p target) :
    target ≤ ((148::a::b::tail).map (· ^ 2)).sum := by
  let input : List ℕ := 148::a::b::tail
  let ws : List ℤ := input.map Int.ofNat
  let t : List ℤ := tail.map Int.ofNat
  let centers : List ℤ := signedSums t
  have nd : (ws.sublists.map List.sum).Nodup := by
    change ((input.map Int.ofNat).sublists.map List.sum).Nodup
    rw [← octCastSublists]
    exact distinct.map (fun _ _ e => Int.ofNat_inj.mp e)
  have sym : signedSums ws = (ws.sublists.map List.sum).map (fun z => 2*z-ws.sum) := by
    simp only [signedSums_eq_centered_sublists, List.map_map, Function.comp_def]
  have signedDistinct : (signedSums ws).Nodup := by
    rw [sym]
    exact nd.map (fun _ _ e => by omega)
  let p := (-ws.sum)%2
  have hp : p=0 ∨ p=1 := by dsimp [p]; omega
  have par : ∀ z ∈ signedSums ws, z%2=p := by
    rw [sym]
    intro z hz
    obtain ⟨q,_,rfl⟩ := List.mem_map.mp hz
    dsimp [p]
    omega
  have decomp : signedSums ws = spread 148 (spread (a : ℤ) (spread (b : ℤ) centers)) := rfl
  have centerPar : ∀ c ∈ centers, (c+(a : ℤ)+(b : ℤ))%2=p := by
    intro c hc
    have q : c-(b : ℤ) ∈ spread (b : ℤ) centers := by
      apply List.mem_flatMap.mpr
      exact ⟨c,hc,by simp⟩
    have qa : c-(b : ℤ)-(a : ℤ) ∈ spread (a : ℤ) (spread (b : ℤ) centers) := by
      apply List.mem_flatMap.mpr
      exact ⟨_,q,by simp⟩
    have hz : c-(b : ℤ)-(a : ℤ)-148 ∈ signedSums ws := by
      rw [decomp]
      apply List.mem_flatMap.mpr
      exact ⟨_,qa,by simp⟩
    have eq := par _ hz
    omega
  let C := cert p hp
  have hc (c : ℤ) (hz : c ∈ centers) :
      C.lambda ≤ octCharge (a : ℤ) (b : ℤ) (fun z => z^2+C.penalty z) c :=
    C.anchor c (centerPar c hz)
  have hch := octCharge_sum_lower _ _ C.lambda (fun z => z^2+C.penalty z) centers hc
  rw [← decomp, List.sum_map_add] at hch
  have hd := selectedPenalty_le_budget (signedSums ws) signedDistinct C.penalty C.box C.positive C.support
  have centerLen : centers.length=64 := by
    simp [centers,t,signedSums_length,len]
  rw [centerLen,signedSums_sum_sq] at hch
  have nine : ws.length=9 := by simp [ws,input,len]
  rw [nine,show (2 : ℤ)^9=512 by decide] at hch
  have sq : (((input.map (· ^ 2)).sum : ℕ) : ℤ) = (ws.map (· ^ 2)).sum := by
    rw [octCastSum]
    simp only [ws,List.map_map]
    congr 1
  rw [←sq] at hch
  have hs : (target : ℤ) ≤ (((input.map (· ^ 2)).sum : ℕ) : ℤ) := by
    have strong := C.strong
    change 512*((target : ℤ)-1) < 64*C.lambda - ∑ z ∈ C.box, C.penalty z at strong
    simp only [Nat.cast_ofNat] at hch
    omega
  exact Int.ofNat_le.mp hs

#print axioms octCharge_check_from_positive_window
#print axioms eightPointNatMomentLower
end NineSeparatedSubsetSums

import NineSeparatedSubsetSums.FourPointPrinciple
import NineSeparatedSubsetSums.PairPackingWeights

open scoped BigOperators

namespace NineSeparatedSubsetSums

/-- Integer certificate for the squared-weight lower bound target for a
fixed second-largest candidate and a fixed parity of its full signed scores. -/
structure FourPointCertificate (a p target : ℤ) where
  lambda : ℤ
  penalty : ℤ → ℤ
  box : Finset ℤ
  positive : ∀ z, 0 ≤ penalty z
  support : ∀ z, z ∉ box → penalty z = 0
  cap : lambda ≤ 4 * (801^2 + 148^2 + a^2)
  anchor : ∀ j : Fin 1601, (((j.val : ℤ)-800)+a)%2=p →
    lambda ≤ blockCharge a (fun z => z^2 + penalty z) ((j.val : ℤ)-800)
  strong : 512 * (target-1) < 128*lambda - ∑ z ∈ box, penalty z

private theorem fourPointCastSum (l : List ℕ) :
    (l.sum : ℤ) = (l.map Int.ofNat).sum := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.sum_cons, List.map_cons, Nat.cast_add, ih]
    rfl

private theorem fourPointCastSublists (l : List ℕ) :
    (natSubsetSums l).map Int.ofNat = (l.map Int.ofNat).sublists.map List.sum := by
  simp only [natSubsetSums, List.sublists_map, List.map_map]
  congr 1
  funext s
  exact fourPointCastSum s

/-- The four-point certificate applies to the actual signed scores for
two designated weights 148 and a. Sorting is not needed for this bound. -/
theorem fourPointNatMomentLower (a target : ℕ) (tail : List ℕ)
    (len : tail.length=7) (distinct : (natSubsetSums (148::a::tail)).Nodup)
    (cert : ∀ p : ℤ, p=0 ∨ p=1 → FourPointCertificate (a : ℤ) p (target : ℤ)) :
    target ≤ ((148::a::tail).map (· ^ 2)).sum := by
  let input : List ℕ := 148::a::tail
  let ws : List ℤ := input.map Int.ofNat
  let t : List ℤ := tail.map Int.ofNat
  let centers : List ℤ := signedSums t
  have nd : (ws.sublists.map List.sum).Nodup := by
    change ((input.map Int.ofNat).sublists.map List.sum).Nodup
    rw [← fourPointCastSublists]
    exact distinct.map (fun _ _ e => Int.ofNat_inj.mp e)
  have sym : signedSums ws = (ws.sublists.map List.sum).map (fun z => 2*z-ws.sum) := by
    simp only [signedSums_eq_centered_sublists, List.map_map, Function.comp_def]
  have signedDistinct : (signedSums ws).Nodup := by
    rw [sym]
    exact nd.map (fun _ _ e => by omega)
  let p := (-ws.sum)%2
  have hp : p=0 ∨ p=1 := by
    dsimp [p]
    omega
  have par : ∀ z ∈ signedSums ws, z%2=p := by
    rw [sym]
    intro z hz
    obtain ⟨q,_,rfl⟩ := List.mem_map.mp hz
    dsimp [p]
    omega
  have decomp : signedSums ws = spread 148 (spread (a : ℤ) centers) := rfl
  have centerPar : ∀ c ∈ centers, (c+(a : ℤ))%2=p := by
    intro c hc
    have q : c-(a : ℤ) ∈ spread (a : ℤ) centers := by
      apply List.mem_flatMap.mpr
      exact ⟨c,hc,by simp⟩
    have hz : c-(a : ℤ)-148 ∈ signedSums ws := by
      rw [decomp]
      apply List.mem_flatMap.mpr
      exact ⟨c-(a : ℤ),q,by simp⟩
    have eq := par _ hz
    omega
  let C := cert p hp
  have charge (c : ℤ) (hc : c ∈ centers) :
      C.lambda ≤ blockCharge (a : ℤ) (fun z => z^2+C.penalty z) c :=
    blockCharge_check_extends _ _ _ _ C.positive C.cap C.anchor c (centerPar c hc)
  have hb := fourPointPacking_lower (a : ℤ) C.lambda centers (decomp ▸ signedDistinct)
    C.penalty C.box C.positive C.support charge
  have centerLen : centers.length=128 := by
    simp [centers,t,signedSums_length,len]
  rw [centerLen, ← decomp, signedSums_sum_sq] at hb
  have nine : ws.length=9 := by
    simp [ws,input,len]
  rw [nine,show (2 : ℤ)^9=512 by decide] at hb
  have sq : (((input.map (· ^ 2)).sum : ℕ) : ℤ) = (ws.map (· ^ 2)).sum := by
    rw [fourPointCastSum]
    simp only [ws,List.map_map]
    congr 1
  rw [← sq] at hb
  have hs : (target : ℤ) ≤ (((input.map (· ^ 2)).sum : ℕ) : ℤ) := by
    have hc := C.strong
    change 512 * ((target : ℤ)-1) < 128 * C.lambda - ∑ z ∈ C.box, C.penalty z at hc
    omega
  exact Int.ofNat_le.mp hs

def fourPointLookupPenalty (T : Array ℕ) (z : ℤ) : ℤ :=
  (T[z.natAbs]?.getD 0 : ℕ)

def fourPointLookupBox (T : Array ℕ) : Finset ℤ :=
  Finset.Icc (-(T.size : ℤ)) (T.size : ℤ)

theorem fourPointLookupPenalty_support (T : Array ℕ) (z : ℤ)
    (out : z ∉ fourPointLookupBox T) : fourPointLookupPenalty T z = 0 := by
  have sz : T.size ≤ z.natAbs := by
    by_contra! h
    apply out
    exact Finset.mem_Icc.mpr (by omega)
  simp [fourPointLookupPenalty, Array.getElem?_eq_none sz]

/-- Convert a literal array into a formal certificate. A producer may
use any external optimizer; the two numeric hypotheses are kernel checked. -/
def fourPointCertificateOfTable (a p target lambda : ℤ) (T : Array ℕ)
    (cap : lambda ≤ 4*(801^2+148^2+a^2))
    (anchor : ∀ j : Fin 1601, (((j.val : ℤ)-800)+a)%2=p →
      lambda ≤ blockCharge a (fun z => z^2+fourPointLookupPenalty T z) ((j.val : ℤ)-800))
    (strong : 512*(target-1) < 128*lambda -
      ∑ z ∈ fourPointLookupBox T, fourPointLookupPenalty T z) :
    FourPointCertificate a p target :=
  ⟨lambda, fourPointLookupPenalty T, fourPointLookupBox T,
    fun _ => Int.natCast_nonneg _, fourPointLookupPenalty_support T, cap, anchor, strong⟩

#print axioms fourPointNatMomentLower
#print axioms fourPointCertificateOfTable

end NineSeparatedSubsetSums

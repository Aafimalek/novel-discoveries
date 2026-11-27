import EulerGeometryCounters
import Mathlib.Logic.Equiv.Fin.Basic

open Finset
open scoped BigOperators
namespace LatinGap.PairEncoding

def freeCoordinatePair (ij : CoordPair) : Coord × Coord :=
  if ij.val.1=0 then
    if ij.val.2=1 then (2,3) else if ij.val.2=2 then (1,3) else (1,2)
  else if ij.val.1=1 then
    if ij.val.2=2 then (0,3) else (0,2)
  else (0,1)

theorem freeCoordinatePair_properties : ∀ ij : CoordPair,
    let f := freeCoordinatePair ij
    f.1<f.2 ∧ f.1≠ij.val.1 ∧ f.1≠ij.val.2 ∧ f.2≠ij.val.1 ∧ f.2≠ij.val.2 ∧
      ∀ g : Coord, g=ij.val.1 ∨ g=ij.val.2 ∨ g=f.1 ∨ g=f.2 := by decide +kernel

def supportFree (p : PairKey 6) : Coord × Coord :=
  freeCoordinatePair ⟨(p.i,p.j),p.increasing⟩

theorem supportFree_properties (p : PairKey 6) :
    let f := supportFree p
    f.1<f.2 ∧ f.1≠p.i ∧ f.1≠p.j ∧ f.2≠p.i ∧ f.2≠p.j ∧
      ∀ g : Coord, g=p.i ∨ g=p.j ∨ g=f.1 ∨ g=f.2 :=
  freeCoordinatePair_properties ⟨(p.i,p.j),p.increasing⟩

/-- Enumerate the 36 words supporting a pair by the two free coordinates
in increasing order, with the latter free coordinate varying fastest. -/
def supportWord (p : PairKey 6) (t : Fin 36) : Word 6 :=
  let z := (finProdFinEquiv : (Fin 6×Fin 6) ≃ Fin 36).symm t
  fun g => if g=p.i then p.a else if g=p.j then p.b else if g=(supportFree p).1 then z.1 else z.2

theorem supportWord_matches (p : PairKey 6) (t : Fin 36) : Matches p (supportWord p t) := by
  have h : p.j≠p.i := (ne_of_lt p.increasing).symm
  constructor <;> simp [supportWord,h]

theorem supportWord_free₁ (p : PairKey 6) (t : Fin 36) :
    supportWord p t (supportFree p).1 =
      ((finProdFinEquiv : (Fin 6×Fin 6) ≃ Fin 36).symm t).1 := by
  obtain ⟨_,hi,hj,_,_,_⟩ := supportFree_properties p
  simp [supportWord,hi,hj]

theorem supportWord_free₂ (p : PairKey 6) (t : Fin 36) :
    supportWord p t (supportFree p).2 =
      ((finProdFinEquiv : (Fin 6×Fin 6) ≃ Fin 36).symm t).2 := by
  obtain ⟨h,_,_,hi,hj,_⟩ := supportFree_properties p
  simp [supportWord,hi,hj,(ne_of_lt h).symm]

theorem supportWord_injective (p : PairKey 6) : Function.Injective (supportWord p) := by
  intro t u h
  apply (finProdFinEquiv : (Fin 6×Fin 6) ≃ Fin 36).symm.injective
  apply Prod.ext
  · simpa only [supportWord_free₁] using congrArg (fun w : Word 6 => w (supportFree p).1) h
  · simpa only [supportWord_free₂] using congrArg (fun w : Word 6 => w (supportFree p).2) h

theorem supportWord_onto (p : PairKey 6) (w : Word 6) (h : Matches p w) :
    ∃ t : Fin 36, supportWord p t = w := by
  let e : (Fin 6×Fin 6) ≃ Fin 36 := finProdFinEquiv
  let t := e (w (supportFree p).1,w (supportFree p).2)
  refine ⟨t,?_⟩
  funext g
  rcases (supportFree_properties p).2.2.2.2.2 g with gi | gj | g₁ | g₂
  · rw [gi]
    exact (supportWord_matches p t).1.trans h.1.symm
  · rw [gj]
    exact (supportWord_matches p t).2.trans h.2.symm
  · rw [g₁,supportWord_free₁]
    change (e.symm (e (w (supportFree p).1,w (supportFree p).2))).1 = _
    rw [e.symm_apply_apply]
  · rw [g₂,supportWord_free₂]
    change (e.symm (e (w (supportFree p).1,w (supportFree p).2))).2 = _
    rw [e.symm_apply_apply]

def supportWordInputId (p : PairKey 6) (i : ℕ) : ℕ :=
  wordNumber (supportWord p ⟨i%36,by omega⟩)

theorem supportWordInputId_fin (p : PairKey 6) (i : Fin 36) :
    supportWordInputId p i.val = wordNumber (supportWord p i) := by
  have e : (⟨i.val%36,by omega⟩ : Fin 36)=i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
  simp [supportWordInputId,e]

/-- A linear geometric design supplies at most one true input for each
of the 216 support counters. -/
theorem geometry_support_prefixOnes (D : Design 6) (linear : Linear D)
    (v : ℕ → Bool) (hword : ∀ w : Word 6, v (wordNumber w) = (encode D).select w)
    (p : PairKey 6) : prefixOnes (fun i => v (supportWordInputId p i)) 36 ≤ 1 := by
  classical
  rw [prefixOnes_as_sum_fin]
  have E : (∑ i : Fin 36, (if v (supportWordInputId p i.val) then 1 else 0 : ℕ)) =
      (univ.filter (fun i : Fin 36 => v (supportWordInputId p i.val)=true)).card := by
    rw [card_filter]
  rw [E]
  apply card_le_one.mpr
  intro i hi j hj
  have e₁ := (mem_filter.mp hi).2
  have e₂ := (mem_filter.mp hj).2
  rw [supportWordInputId_fin,hword,select_encode] at e₁ e₂
  have iMatch := supportWord_matches p i
  have jMatch := supportWord_matches p j
  exact supportWord_injective p (linear e₁ e₂ (ne_of_lt p.increasing)
    (iMatch.1.trans jMatch.1.symm) (iMatch.2.trans jMatch.2.symm))

#print axioms supportWord_injective
#print axioms supportWord_onto
#print axioms geometry_support_prefixOnes

end LatinGap.PairEncoding

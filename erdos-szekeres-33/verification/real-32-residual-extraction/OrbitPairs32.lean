/- Static, uncompiled orbit-list draft. Deliberately independent of the
real geometry stack. No DIMACS definition or imported solver is involved. -/
import Lean

namespace ES33.OrbitPairs32

abbrev Triple := Fin 32 × Fin 32 × Fin 32

def rev (t : Triple) : Triple :=
  (Fin.rev t.2.2, Fin.rev t.2.1, Fin.rev t.1)

def Ordered (t : Triple) : Prop := t.1 < t.2.1 ∧ t.2.1 < t.2.2

/-- Compare the first coordinate to the reflected first coordinate.
If they tie, compare the middle coordinates (which cannot tie). -/
def Representative (t : Triple) : Prop :=
  t.1.val+t.2.2.val < 31 ∨
    (t.1.val+t.2.2.val = 31 ∧ t.2.1.val ≤ 15)

def repBit (t : Triple) : Bool :=
  decide (t.1.val+t.2.2.val < 31 ∨
    (t.1.val+t.2.2.val = 31 ∧ t.2.1.val ≤ 15))

theorem rev_rev (t : Triple) : rev (rev t) = t := by
  rcases t with ⟨a,b,c⟩
  simp [rev]

theorem ordered_rev {t : Triple} (h : Ordered t) : Ordered (rev t) :=
  ⟨Fin.rev_lt_rev.mpr h.2,Fin.rev_lt_rev.mpr h.1⟩

theorem representative_rev_iff (t : Triple) :
    Representative (rev t) ↔ ¬ Representative t := by
  rcases t with ⟨a,b,c⟩
  have ha := a.isLt
  have hb := b.isLt
  have hc := c.isLt
  simp only [Representative,rev,Fin.val_rev]
  omega

theorem rev_ne_self (t : Triple) : rev t ≠ t := by
  intro he
  have H := representative_rev_iff t
  rw [he] at H
  by_cases ht : Representative t
  · exact (H.mp ht) ht
  · exact ht (H.mpr ht)

/-- Enumerate all ordered triples in nested increasing rank order. -/
def all32 : List Triple :=
  (List.finRange 32).flatMap fun a =>
    ((List.finRange 32).filter (fun b => decide (a<b))).flatMap fun b =>
      ((List.finRange 32).filter (fun c => decide (b<c))).map fun c => (a,b,c)

def reps32 : List Triple := all32.filter repBit

theorem mem_all32 {t : Triple} : t ∈ all32 ↔ Ordered t := by
  rcases t with ⟨a,b,c⟩
  constructor
  · intro h
    unfold all32 at h
    obtain ⟨i,_,hi⟩ := List.mem_flatMap.mp h
    obtain ⟨j,hj,hij⟩ := List.mem_flatMap.mp hi
    obtain ⟨k,hk,he⟩ := List.mem_map.mp hij
    have ei : i=a := congrArg Prod.fst he
    have ej : j=b := congrArg (fun q : Triple => q.2.1) he
    have ek : k=c := congrArg (fun q : Triple => q.2.2) he
    subst i
    subst j
    subst k
    exact ⟨of_decide_eq_true (List.mem_filter.mp hj).2,
      of_decide_eq_true (List.mem_filter.mp hk).2⟩
  · intro h
    unfold all32
    exact List.mem_flatMap.mpr ⟨a,List.mem_finRange a,
      List.mem_flatMap.mpr ⟨b,
        List.mem_filter.mpr ⟨List.mem_finRange b,decide_eq_true h.1⟩,
        List.mem_map.mpr ⟨c,List.mem_filter.mpr ⟨List.mem_finRange c,decide_eq_true h.2⟩,rfl⟩⟩⟩

theorem mem_reps32 {t : Triple} :
    t ∈ reps32 ↔ Ordered t ∧ Representative t := by
  simp [reps32,repBit,mem_all32,Representative]

theorem exactly_one_rep {t : Triple} (ht : Ordered t) :
    (t ∈ reps32 ∧ rev t ∉ reps32) ∨ (rev t ∈ reps32 ∧ t ∉ reps32) := by
  by_cases h : Representative t
  · exact Or.inl ⟨mem_reps32.mpr ⟨ht,h⟩,
      fun H => ((representative_rev_iff t).mp (mem_reps32.mp H).2) h⟩
  · exact Or.inr ⟨mem_reps32.mpr ⟨ordered_rev ht,(representative_rev_iff t).mpr h⟩,
      fun H => h (mem_reps32.mp H).2⟩

/-- Numerical and list-order checkpoints for a future separate build.
These propositions are not asserted or proved by the static draft. -/
def CountCheckpoint : Prop := all32.length=4960 ∧ reps32.length=2480

#print axioms representative_rev_iff
#print axioms rev_ne_self
#print axioms mem_all32
#print axioms exactly_one_rep

end ES33.OrbitPairs32

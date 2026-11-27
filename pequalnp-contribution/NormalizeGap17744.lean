import PEqualNP.Defs
import Mathlib.Tactic


namespace SingerFlag
open PEqualNP.HeptadCover

structure Relabel where
  points : Fin 13 ≃ Fin 13
  lines : Fin 13 ≃ Fin 13
  inc : ∀ p l, p ∈ singerLines3 l ↔ points p ∈ singerLines3 (lines l)

def Relabel.trans (a b : Relabel) : Relabel :=
  ⟨a.points.trans b.points, a.lines.trans b.lines, fun p l =>
    (a.inc p l).trans (b.inc (a.points p) (a.lines l))⟩

def Relabel.refl : Relabel := ⟨Equiv.refl _, Equiv.refl _, fun _ _ => Iff.rfl⟩

def Relabel.symm (a : Relabel) : Relabel :=
  ⟨a.points.symm, a.lines.symm, fun p l => by
    simpa using (a.inc (a.points.symm p) (a.lines.symm l)).symm⟩

private def P (p : Fin 13) : Fin 13 := ![1,3,2,9,5,6,12,8,4,0,11,7,10] p
private def P' (p : Fin 13) : Fin 13 := ![9,0,2,1,8,4,5,11,7,3,12,10,6] p
private def L (l : Fin 13) : Fin 13 := ![0,2,6,9,5,3,12,8,4,10,11,7,1] l
private def L' (l : Fin 13) : Fin 13 := ![0,12,1,5,8,4,2,11,7,3,9,10,6] l

set_option maxRecDepth 12000 in
set_option maxHeartbeats 1000000 in
private theorem cycle_inc_aux : ∀ p l, p ∈ singerLines3 l ↔ P p ∈ singerLines3 (L l) := by decide

private def cycle : Relabel where
  points := ⟨P, P', by decide, by decide⟩
  lines := ⟨L, L', by decide, by decide⟩
  inc := cycle_inc_aux

private theorem shift_inc (k p l : Fin 13) :
    p ∈ singerLines3 l ↔ p - k ∈ singerLines3 (l - k) := by
  simp only [singerLines3, Finset.mem_filter, Finset.mem_univ, true_and]
  have eq (i j : Fin 13) : (i.val + 13 - j.val) % 13 = (i-j).val := by
    rw [Fin.val_sub]
    congr 1
    have hj := j.isLt
    omega
  rw [eq, eq, sub_sub_sub_cancel_right]

private def shift (k : Fin 13) : Relabel :=
  ⟨Equiv.subRight k, Equiv.subRight k, shift_inc k⟩

private theorem rotation : ∀ p, p ∈ singerLines3 0 → ∃ i : Fin 4,
    (match i.val with
      | 0 => Relabel.refl
      | 1 => cycle
      | 2 => cycle.trans cycle
      | _ => (cycle.trans cycle).trans cycle).points p = 0 := by
  decide

theorem normalize (p l : Fin 13) (h : p ∈ singerLines3 l) :
    ∃ a : Relabel, a.points p = 0 ∧ a.lines l = 0 := by
  let rots : Fin 4 → Relabel := fun i =>
    match i.val with
    | 0 => Relabel.refl
    | 1 => cycle
    | 2 => cycle.trans cycle
    | _ => (cycle.trans cycle).trans cycle
  have hb : (shift l).points p ∈ singerLines3 0 := by
    have aux := (shift l).inc p l |>.mp h
    simpa [shift, Equiv.subRight_apply] using aux
  obtain ⟨i, hi⟩ := rotation _ hb
  have hline : ∀ j : Fin 4, (rots j).lines 0 = 0 := by decide
  refine ⟨(shift l).trans (rots i), hi, ?_⟩
  change (rots i).lines (l - l) = 0
  rw [sub_self, hline]


theorem Relabel.map_line (a : Relabel) (l : Fin 13) :
    (singerLines3 l).map a.points.toEmbedding = singerLines3 (a.lines l) := by
  ext q
  obtain ⟨p, rfl⟩ := a.points.surjective q
  rw [← a.inc p l]
  simp

theorem Relabel.map_quadrangle (a : Relabel) (Q : Finset (Fin 13)) :
    Q ∈ quadrangles singerLines3 ↔ Q.map a.points.toEmbedding ∈ quadrangles singerLines3 := by
  simp only [quadrangles, Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ,
    Finset.card_map, true_and]
  constructor
  · rintro ⟨hc, h⟩
    refine ⟨hc, fun l => ?_⟩
    obtain ⟨j, rfl⟩ := a.lines.surjective l
    rw [← a.map_line j, ← Finset.map_inter, Finset.card_map]
    exact h j
  · rintro ⟨hc, h⟩
    refine ⟨hc, fun l => ?_⟩
    simpa [← a.map_line l, ← Finset.map_inter] using h (a.lines l)

theorem Relabel.map_missLines (a : Relabel) (Q : Finset (Fin 13)) :
    (missLines singerLines3 Q).map a.lines.toEmbedding =
      missLines singerLines3 (Q.map a.points.toEmbedding) := by
  ext l
  obtain ⟨j, rfl⟩ := a.lines.surjective l
  simp only [Finset.mem_map_equiv, Equiv.symm_apply_apply,
    missLines, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← a.map_line j]
  simp

#print axioms normalize
end SingerFlag


namespace RelabelCircuit
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def gate (f : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map f⟩
def rename (f : ℕ → ℕ) (c : Circuit) : Circuit := ⟨c.gates.map (gate f), f c.output⟩

@[simp] theorem rename_size (f : ℕ → ℕ) (c : Circuit) : (rename f c).size = c.size := by
  simp [rename, Circuit.size]

theorem rename_monotone (f : ℕ → ℕ) (c : Circuit) (h : Monotone2 c) : Monotone2 (rename f c) := by
  intro g hg
  obtain ⟨g₀, hg₀, rfl⟩ := List.mem_map.mp hg
  simpa [gate] using h g₀ hg₀

private theorem extend (f : ℕ → ℕ) {n : ℕ}
    (below : ∀ i < n, f i < n) (above : ∀ i ≥ n, f i = i)
    (x y : List Bool) (hxy : x.length = y.length) (hn : n ≤ x.length)
    (agree : ∀ i, x.getD i false = y.getD (f i) false) (b : Bool) :
    ∀ i, (x ++ [b]).getD i false = (y ++ [b]).getD (f i) false := by
  intro i
  by_cases hi : i < x.length
  · have hfi : f i < y.length := by
      rw [← hxy]
      by_cases hin : i < n
      · exact (below i hin).trans_le hn
      · rw [above i (by omega)]
        exact hi
    simpa [List.getD_eq_getElem?_getD, List.getElem?_append, hi, hfi] using agree i
  · have hfi : f i = i := above i (by omega)
    rw [hfi]
    have hiy : ¬i < y.length := by omega
    simp [List.getD_eq_getElem?_getD, List.getElem?_append, hiy, hxy]

private theorem foldl_agree (f : ℕ → ℕ) {n : ℕ}
    (below : ∀ i < n, f i < n) (above : ∀ i ≥ n, f i = i)
    (gs : List Gate) (x y : List Bool) (hxy : x.length = y.length) (hn : n ≤ x.length)
    (agree : ∀ i, x.getD i false = y.getD (f i) false) :
    ∀ i, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) x).getD i false =
      ((gs.map (gate f)).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) y).getD (f i) false := by
  induction gs generalizing x y with
  | nil => exact agree
  | cons g gs ih =>
    simp only [List.foldl_cons, List.map_cons]
    let b := g.op.eval (g.inputs.map fun j => x.getD j false)
    have hb : (gate f g).op.eval ((gate f g).inputs.map fun j => y.getD j false) = b := by
      simp only [gate, List.map_map, b]
      congr 1
      apply List.map_congr_left
      intro i _
      exact (agree i).symm
    rw [hb]
    exact ih _ _ (by simp [hxy]) (by simp; omega) (extend f below above x y hxy hn agree b)

theorem eval_rename (f : ℕ → ℕ) {n : ℕ}
    (below : ∀ i < n, f i < n) (above : ∀ i ≥ n, f i = i)
    (c : Circuit) (x y : List Bool) (hxy : x.length = y.length) (hn : n ≤ x.length)
    (agree : ∀ i, x.getD i false = y.getD (f i) false) :
    c.eval x = (rename f c).eval y :=
  foldl_agree f below above c.gates x y hxy hn agree c.output

#print axioms eval_rename
end RelabelCircuit


namespace GapSymmetry
open PEqualNP.HeptadCover PEqualNP.GenericRejection PEqualNP.CircuitLowerBounds
  PEqualNP.MetaComplexity SingerFlag RelabelCircuit

def wire (a : Relabel) (i : ℕ) : ℕ :=
  if h : i < 13 then (a.points ⟨i, h⟩).val
  else if h' : i - 13 < 13 then 13 + (a.lines ⟨i - 13, h'⟩).val
  else i

private theorem wire_below (a : Relabel) (i : ℕ) (hi : i < 26) : wire a i < 26 := by
  unfold wire
  split
  · rename_i h
    have := (a.points ⟨i,h⟩).isLt
    omega
  · split
    · rename_i h
      have := (a.lines ⟨i - 13,h⟩).isLt
      omega
    · omega

private theorem wire_above (a : Relabel) (i : ℕ) (hi : 26 ≤ i) : wire a i = i := by
  unfold wire
  rw [dite_eq_right (by omega), dite_eq_right (by omega)]

private theorem agree (a : Relabel) (X Y : Finset (Fin 13)) (i : ℕ) :
    (incidenceInput X Y).getD i false =
      (incidenceInput (X.map a.points.toEmbedding) (Y.map a.lines.toEmbedding)).getD (wire a i) false := by
  simp only [incidenceInput, List.getD_eq_getElem?_getD, List.getElem?_append, List.length_ofFn]
  by_cases hp : i < 13
  · let p : Fin 13 := ⟨i, hp⟩
    have hq : (a.points p).val < 13 := (a.points p).isLt
    rw [show wire a i = (a.points p).val by simp [wire, hp, p]]
    simp only [hp, hq, dite_true, ite_true, List.getElem?_ofFn, Option.getD_some,
      Finset.mem_map_equiv, p]
    congr 1
    simp
  · by_cases hl : i - 13 < 13
    · let l : Fin 13 := ⟨i - 13, hl⟩
      have hq : (a.lines l).val < 13 := (a.lines l).isLt
      rw [show wire a i = 13 + (a.lines l).val by simp [wire, hp, hl, l]]
      have hnum : ¬ 13 + (a.lines l).val < 13 := by omega
      simp only [hp, hnum, ite_false, Nat.add_sub_cancel_left, List.getElem?_ofFn, hq, hl,
        dite_true, Option.getD_some, Finset.mem_map_equiv, l]
      congr 1
      simp
    · rw [wire_above a i (by omega)]
      simp only [hp, hl, ite_false, List.getElem?_ofFn, dite_false]

theorem eval_transport (a : Relabel) (c : Circuit) (X Y : Finset (Fin 13)) :
    c.eval (incidenceInput X Y) =
      (rename (wire a) c).eval
        (incidenceInput (X.map a.points.toEmbedding) (Y.map a.lines.toEmbedding)) := by
  refine eval_rename (wire a) (n := 26) (wire_below a) (wire_above a) c _ _ ?_ ?_ (agree a X Y)
  all_goals simp [incidenceInput]

def hit (p l : Fin 13) (c : Circuit) : Finset (Finset (Fin 13)) :=
  {Q ∈ quadrangles singerLines3 |
    c.eval (incidenceInput (Q.erase p) ((missLines singerLines3 Q).erase l)) = true}

def GapAt (p l : Fin 13) : Prop :=
  ∀ c d : Circuit, c.gates = d.gates → Monotone2 c →
    (∀ q m : Fin 13, q ≠ p → m ≠ l → q ∈ singerLines3 m →
      ∀ e ∈ [c, d], e.eval (incidenceInput {q} {m}) = true) →
    Disjoint (hit p l c) (hit p l d) → (hit p l c).Nonempty → (hit p l d).Nonempty →
    56 ≤ c.size

private theorem hit_transport (a : Relabel) (c : Circuit) (p l : Fin 13) (Q : Finset (Fin 13)) :
    Q ∈ hit p l c ↔
      Q.map a.points.toEmbedding ∈ hit (a.points p) (a.lines l) (rename (wire a) c) := by
  simp only [hit, Finset.mem_filter]
  rw [← a.map_quadrangle Q]
  rw [eval_transport a c (Q.erase p) ((missLines singerLines3 Q).erase l),
    Finset.map_erase, Finset.map_erase, a.map_missLines]
  rfl

theorem transfer (a : Relabel) (p l : Fin 13) (h : GapAt (a.points p) (a.lines l)) : GapAt p l := by
  intro c d hg hm hp hdis hc hd
  have positives (q m : Fin 13) (hq : q ≠ p) (hl : m ≠ l) (hi : q ∈ singerLines3 m)
      (e : Circuit) (he : e ∈ [c,d]) :
      (rename (wire a) e).eval (incidenceInput {a.points q} {a.lines m}) = true := by
    simpa using (eval_transport a e {q} {m}).symm.trans (hp q m hq hl hi e he)
  have hpos (q m : Fin 13) (hq : q ≠ a.points p) (hl : m ≠ a.lines l)
      (hi : q ∈ singerLines3 m) (e : Circuit)
      (he : e ∈ [rename (wire a) c, rename (wire a) d]) :
      e.eval (incidenceInput {q} {m}) = true := by
    obtain ⟨q₀, rfl⟩ := a.points.surjective q
    obtain ⟨m₀, rfl⟩ := a.lines.surjective m
    have hq₀ : q₀ ≠ p := fun h => hq (congrArg a.points h)
    have hl₀ : m₀ ≠ l := fun h => hl (congrArg a.lines h)
    have hi₀ : q₀ ∈ singerLines3 m₀ := (a.inc q₀ m₀).mpr hi
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
    rcases he with rfl | rfl
    · exact positives q₀ m₀ hq₀ hl₀ hi₀ c (by simp)
    · exact positives q₀ m₀ hq₀ hl₀ hi₀ d (by simp)
  have hdis' : Disjoint (hit (a.points p) (a.lines l) (rename (wire a) c))
      (hit (a.points p) (a.lines l) (rename (wire a) d)) := by
    apply Finset.disjoint_left.mpr
    intro Q hQ₁ hQ₂
    let Q₀ := Q.map a.points.symm.toEmbedding
    have hQ : Q₀.map a.points.toEmbedding = Q := by
      ext z
      simp [Q₀, Finset.mem_map_equiv]
    rw [← hQ] at hQ₁ hQ₂
    exact Finset.disjoint_left.mp hdis ((hit_transport a c p l Q₀).mpr hQ₁)
      ((hit_transport a d p l Q₀).mpr hQ₂)
  have hc' : (hit (a.points p) (a.lines l) (rename (wire a) c)).Nonempty := by
    obtain ⟨Q, hQ⟩ := hc
    exact ⟨Q.map a.points.toEmbedding, (hit_transport a c p l Q).mp hQ⟩
  have hd' : (hit (a.points p) (a.lines l) (rename (wire a) d)).Nonempty := by
    obtain ⟨Q, hQ⟩ := hd
    exact ⟨Q.map a.points.toEmbedding, (hit_transport a d p l Q).mp hQ⟩
  simpa using h (rename (wire a) c) (rename (wire a) d)
    (by simp [rename, hg]) (rename_monotone (wire a) c hm) hpos hdis' hc' hd'

theorem reduction : GapAt 0 0 ↔ ∀ p l : Fin 13, p ∈ singerLines3 l → GapAt p l := by
  constructor
  · intro h p l hflag
    obtain ⟨a, hp, hl⟩ := normalize p l hflag
    exact transfer a p l (by simpa [hp,hl] using h)
  · intro h
    exact h 0 0 (by decide)

#print axioms reduction
end GapSymmetry

/-- L-meta-17744 is equivalent to its single normalized incidence flag. -/
theorem gap17744_iff_normalized : GapSymmetry.GapAt 0 0 ↔
    (have x1 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ)) := PEqualNP.HeptadCover.singerLines3; ∀ (x2 x3 : Fin (13 : ℕ)) (x4 x5 : PEqualNP.CircuitLowerBounds.Circuit),   x2 ∈ x1 x3 →     x4.gates = x5.gates →       PEqualNP.MetaComplexity.Monotone2 x4 →         (∀ (x9 x10 : Fin (13 : ℕ)), x9 ≠ x2 → x10 ≠ x3 → x9 ∈ x1 x10 → ∀ x14 ∈ [x4, x5], x14.eval (PEqualNP.GenericRejection.incidenceInput {x9} {x10}) = Bool.true) →           have x10 : PEqualNP.CircuitLowerBounds.Circuit → Finset (Finset (Fin (13 : ℕ))) := fun (x10 : PEqualNP.CircuitLowerBounds.Circuit) => {x11 ∈ PEqualNP.HeptadCover.quadrangles x1 | x10.eval (PEqualNP.GenericRejection.incidenceInput (x11.erase x2) ((PEqualNP.HeptadCover.missLines x1 x11).erase x3)) = Bool.true};           Disjoint (x10 x4) (x10 x5) → (x10 x4).Nonempty → (x10 x5).Nonempty → (56 : ℕ) ≤ x4.size) := by
  rw [GapSymmetry.reduction]
  constructor
  · intro h x1 p l c d hflag
    exact h p l hflag c d
  · intro h p l hflag c d
    exact h p l c d hflag

#print axioms gap17744_iff_normalized

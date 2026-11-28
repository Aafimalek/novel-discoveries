import Init

set_option warningAsError true
/-! A purely abstract layer-and-block lemma.
It neither defines number fields nor assumes any unproved facts about them. -/

namespace LayeredFive

universe u v

/-- The positive levels are processed in increasing order.
For a lower neighbor, the target stores its color data rather than a
color assigned by the as-yet-undefined recursion. -/
structure Scheme (V : Type u) (B : Type v) where
  edge : V → V → Prop
  level : V → Nat
  block : V → B
  residue : V → Fin 4
  base : V → Fin 5
  target : B → Option V
  edge_symm : ∀ {x y}, edge x y → edge y x
  base_proper : ∀ {x y}, edge x y → level x = 0 → level y = 0 →
    base x ≠ base y
  target_lt : ∀ {x t}, level x ≠ 0 → target (block x) = some t →
    level t < level x
  same_level : ∀ {x y}, edge x y → level x = level y → level x ≠ 0 →
    block x = block y ∧ residue x ≠ residue y
  lower_neighbor : ∀ {x y}, edge x y → level y < level x →
    ∃ t, target (block x) = some t ∧ level y = level t ∧
      ((level y = 0 ∧ base y = base t) ∨
       (level y ≠ 0 ∧ block y = block t ∧ residue y = residue t))

/-- Insert a gap at the forbidden color. -/
private def skip (c : Fin 5) (i : Fin 4) : Fin 5 :=
  ⟨if i.val < c.val then i.val else i.val + 1, by
    have hi := i.isLt
    split <;> omega⟩

private theorem skip_ne (c : Fin 5) (i : Fin 4) : skip c i ≠ c := by
  intro h
  have hval := congrArg Fin.val h
  change (if i.val < c.val then i.val else i.val + 1) = c.val at hval
  split at hval <;> omega

private theorem skip_injective (c : Fin 5) {i j : Fin 4} :
    skip c i = skip c j → i = j := by
  intro h
  apply Fin.ext
  have hval := congrArg Fin.val h
  change
    (if i.val < c.val then i.val else i.val + 1) =
    (if j.val < c.val then j.val else j.val + 1) at hval
  split at hval <;> split at hval <;> omega

private def lastColor : Fin 5 := ⟨4, by decide⟩

namespace Scheme

variable {V : Type u} {B : Type v} (G : Scheme V B)

private theorem level_wf :
    WellFounded (fun y x : V => G.level y < G.level x) :=
  InvImage.wf G.level Nat.lt_wfRel.wf

private def colorStep (x : V)
    (earlier : (y : V) → G.level y < G.level x → Fin 5) : Fin 5 :=
  if hx : G.level x = 0 then G.base x
  else
    match h : G.target (G.block x) with
    | none => skip lastColor (G.residue x)
    | some t => skip (earlier t (G.target_lt hx h)) (G.residue x)

/-- The color map defined by well-founded recursion on the level. -/
noncomputable def color : V → Fin 5 :=
  (level_wf G).fix (C := fun _ => Fin 5) (colorStep G)

private theorem color_step (x : V) :
    G.color x = colorStep G x (fun y _ => G.color y) :=
  WellFounded.fix_eq (level_wf G) (colorStep G) x

private noncomputable def forbidden (b : B) : Fin 5 :=
  match G.target b with
  | none => lastColor
  | some t => G.color t

theorem color_at_zero {x : V} (hx : G.level x = 0) :
    G.color x = G.base x := by
  rw [color_step G x]
  simp [colorStep, hx]

private theorem color_pos {x : V} (hx : G.level x ≠ 0) :
    G.color x = skip (forbidden G (G.block x)) (G.residue x) := by
  rw [color_step G x]
  simp only [colorStep, dite_eq_right hx]
  split <;> simp [forbidden, *]

private theorem lower_proper {x y : V} (e : G.edge x y)
    (h : G.level y < G.level x) : G.color x ≠ G.color y := by
  have hx : G.level x ≠ 0 := by omega
  obtain ⟨t, htarget, hlevel, heq⟩ := G.lower_neighbor e h
  have hyt : G.color y = G.color t := by
    rcases heq with ⟨hy, hbase⟩ | ⟨hy, hblock, hres⟩
    · have ht : G.level t = 0 := hlevel.symm.trans hy
      rw [color_at_zero G hy, color_at_zero G ht, hbase]
    · have ht : G.level t ≠ 0 := fun ht => hy (hlevel.trans ht)
      rw [color_pos G hy, color_pos G ht, hblock, hres]
  rw [color_pos G hx, hyt]
  simpa only [forbidden, htarget] using skip_ne (G.color t) (G.residue x)

/-- Every unit-edge abstracted by the scheme has distinct endpoint colors. -/
theorem proper {x y : V} (e : G.edge x y) :
    G.color x ≠ G.color y := by
  rcases Nat.lt_trichotomy (G.level x) (G.level y) with h | h | h
  · exact (lower_proper G (G.edge_symm e) h).symm
  · by_cases hx : G.level x = 0
    · have hy : G.level y = 0 := h.symm.trans hx
      rw [color_at_zero G hx, color_at_zero G hy]
      exact G.base_proper e hx hy
    · have hy : G.level y ≠ 0 := fun hy => hx (h.trans hy)
      obtain ⟨hblock, hres⟩ := G.same_level e h hx
      rw [color_pos G hx, color_pos G hy, hblock]
      intro hc
      exact hres (skip_injective (forbidden G (G.block y)) hc)
  · exact lower_proper G e h

theorem exists_proper_five :
    ∃ c : V → Fin 5, ∀ {x y}, G.edge x y → c x ≠ c y :=
  ⟨G.color, fun e => G.proper e⟩

end Scheme

#print axioms Scheme.exists_proper_five

end LayeredFive

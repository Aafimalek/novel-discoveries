from pathlib import Path
T=[[int(x) for x in s.strip()] for s in Path('colors.txt').read_text().splitlines()]
assert len(T)==17 and all(len(r)==17 and all(0<=i<=5 for i in r) for r in T)
D=[(a,b) for a in range(17) for b in range(17) if (a*a+3*b*b)%17==1]
assert len(D)==18
assert all(T[b][a]!=T[(b+db)%17][(a+da)%17] for a in range(17) for b in range(17) for da,db in D)
print('independent exact check:',len(D),'directions,',17*17*len(D)//2,'unordered edges; color counts',[sum(row.count(c) for row in T) for c in range(6)])
codes=[sum(i*(8**a) for a,i in enumerate(r)) for r in T]
assert all((codes[b]//(8**a))%8==T[b][a] for a in range(17) for b in range(17))
table=', '.join(map(str,codes))
dirs=', '.join(f'({a}, {b})' for a,b in D)
cases=' | '.join('h' for _ in range(17))
cover=' ∨ '.join(f'b = {i}' for i in range(17))
rows='\n'.join(f'theorem row{i} : RowProper {i} := by decide' for i in range(17))
caseproofs='\n'.join(f'  · exact h.symm ▸ row{i}' for i in range(17))
Path('F17ResidueTable.lean').write_text(f'''import Init

namespace HadwigerNelson.F17Residue
set_option maxHeartbeats 3000000
set_option maxRecDepth 16000

abbrev Coord := Fin 17
abbrev Colour := Fin 6

def table : Array Nat := #[
  {table}
]

def color (a b : Coord) : Colour :=
  ⟨(((table[b.val]?).getD 0) / 8^a.val % 8) % 6, Nat.mod_lt _ (by decide)⟩

def normOne (a b : Coord) : Prop := (a.val*a.val+3*b.val*b.val)%17=1

instance (a b : Coord) : Decidable (normOne a b) := by
  unfold normOne
  infer_instance

def dirs : Array (Coord × Coord) := #[{dirs}]

def direction (i : Fin 18) : Coord × Coord := (dirs[i.val]?).getD (0,0)

theorem hasDirection :
    ∀ (da db : Coord), normOne da db → ∃ i : Fin 18, direction i = (da, db) := by decide

def move (a d : Coord) : Coord := ⟨(a.val+d.val)%17, Nat.mod_lt _ (by decide)⟩

def diff (a a' : Coord) : Coord := ⟨(a'.val+17-a.val)%17, Nat.mod_lt _ (by decide)⟩

theorem move_diff : ∀ (a a' : Coord), move a (diff a a') = a' := by decide

def RowProper (b : Coord) : Prop :=
  ∀ (a : Coord) (i : Fin 18), color a b ≠ color (move a (direction i).1) (move b (direction i).2)

instance (b : Coord) : Decidable (RowProper b) := by
  unfold RowProper
  infer_instance

{rows}

theorem rowCover : ∀ (b : Coord), {cover} := by decide

theorem row_proper (b : Coord) : RowProper b := by
  rcases rowCover b with {cases}
{caseproofs}

theorem proper_unit_direction (a b da db : Coord) (h : normOne da db) :
    color a b ≠ color (move a da) (move b db) := by
  obtain ⟨i, hi⟩ := hasDirection da db h
  have good := row_proper b a i
  rw [hi] at good
  exact good

theorem proper_norm_one_difference (a b a' b' : Coord)
    (h : normOne (diff a a') (diff b b')) : color a b ≠ color a' b' := by
  have good := proper_unit_direction a b (diff a a') (diff b b') h
  rw [move_diff a a', move_diff b b'] at good
  exact good

#print axioms hasDirection
#print axioms row_proper
#print axioms proper_norm_one_difference

end HadwigerNelson.F17Residue
''')

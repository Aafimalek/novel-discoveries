/- Static 24-row contiguous packet proof. No Lean process has run. -/
import PacketInternalPilot
import Packet24Text

namespace ES33.EndpointConcrete.Packet24

open ES33.Numbering

private def signTable32 : List (Key 32) :=
  (triples 32).map (fun (a,b,c) => .sign a b c)

private def signPrefix : List (Key 32) := signTable32.take 469

private def sideTail32 : List (Key 32) :=
  sideDictionary 32 7 .cap ++ sideDictionary 32 6 .cup

private theorem append_cut {V : Type} (d t : List V) (k : Nat) :
    d ++ t = d.take k ++ (d.drop k ++ t) := by
  calc
    d ++ t = (d.take k ++ d.drop k) ++ t :=
      congrArg (fun xs : List V => xs ++ t) (List.take_append_drop k d).symm
    _ = _ := List.append_assoc _ _ _

private theorem dict_split :
    dictionary 32 7 6 = signPrefix ++ (signTable32.drop 469 ++ sideTail32) := by
  change (signTable32 ++ sideDictionary 32 7 .cap) ++ sideDictionary 32 6 .cup = _
  calc
    _ = signTable32 ++ sideTail32 := List.append_assoc _ _ _
    _ = _ := append_cut signTable32 sideTail32 469

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem prefix_length : signPrefix.length = 469 := by decide

private theorem id_of_prefix {v : Key 32} {i : Nat}
    (hi : signPrefix.idxOf v + 1 = i) (hb : i≤469) : productionId32 v = i := by
  have hlen := prefix_length
  have hm : v ∈ signPrefix := List.idxOf_lt_length_iff.mp (by omega)
  unfold productionId32
  rw [dict_split,List.idxOf_append,ite_eq_left hm]
  exact hi

section
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

private theorem id_014 : productionId32 (.sign 0 1 4) = 3 :=
  id_of_prefix (by decide) (by decide)
private theorem id_024 : productionId32 (.sign 0 2 4) = 32 :=
  id_of_prefix (by decide) (by decide)
private theorem id_124 : productionId32 (.sign 1 2 4) = 467 :=
  id_of_prefix (by decide) (by decide)
private theorem id_015 : productionId32 (.sign 0 1 5) = 4 :=
  id_of_prefix (by decide) (by decide)
private theorem id_025 : productionId32 (.sign 0 2 5) = 33 :=
  id_of_prefix (by decide) (by decide)
private theorem id_125 : productionId32 (.sign 1 2 5) = 468 :=
  id_of_prefix (by decide) (by decide)
private theorem id_016 : productionId32 (.sign 0 1 6) = 5 :=
  id_of_prefix (by decide) (by decide)
private theorem id_026 : productionId32 (.sign 0 2 6) = 34 :=
  id_of_prefix (by decide) (by decide)
private theorem id_126 : productionId32 (.sign 1 2 6) = 469 :=
  id_of_prefix (by decide) (by decide)

end

abbrev Quad := Fin 32 × Fin 32 × Fin 32 × Fin 32

private def four : List Quad := [(0,1,2,3),(0,1,2,4),(0,1,2,5),(0,1,2,6)]

private def expand : Quad → CNF (Key 32) :=
  fun (a,b,c,e) => packetRows a b c e

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem production_quartet_prefix : (packets 32).take 4 = four := by decide

/-- The rows come from an actual prefix of the production packet list. -/
def typedPrefix : CNF (Key 32) := ((packets 32).take 4).flatMap expand

theorem packet24_exact : encode productionId32 typedPrefix = ExternalPacket24.expected := by
  simp [typedPrefix,production_quartet_prefix,four,expand,packetRows,encode,signed,flip,sign,
    production_id_012,production_id_013,production_id_023,production_id_123,
    id_014,id_024,id_124,id_015,id_025,id_125,id_016,id_026,id_126,
    ExternalPacket24.expected]

private theorem scope_encode {V : Type} [BEq V] (keys : List V) (F : CNF V)
    (supports : Supports keys F) :
    compile keys F supports = encode (fun v => keys.idxOf v+1) F := by
  unfold compile encode scope
  rw [List.map_map]
  refine (List.map_congr_left ?_).trans
    (List.attach_map_val (l := F) (f := fun row => row.map (signed (fun v => keys.idxOf v+1))))
  intro row _
  change (scopeClause keys row.val (supports row.val row.property)).map
    (signed (index keys)) = _
  unfold scopeClause
  rw [List.map_map]
  exact List.attach_map_val (l := row.val) (f := signed (fun v => keys.idxOf v+1))

private def pre : CNF (Key 32) :=
  sideRows 32 7 .cap ++ sideRows 32 6 .cup ++ crossRows 32 7 7 6

private def post : CNF (Key 32) := ((packets 32).drop 4).flatMap expand

private theorem typed_split : typedRows 32 7 7 6 = pre ++ (typedPrefix ++ post) := by
  change pre ++ (packets 32).flatMap expand = pre ++ (typedPrefix ++ post)
  have hp : (packets 32).flatMap expand = typedPrefix ++ post := by
    unfold typedPrefix post
    rw [← List.flatMap_append,List.take_append_drop]
  exact congrArg (fun xs : CNF (Key 32) => pre ++ xs) hp

private theorem encode_append {V : Type} (id : V → Nat) (x y : CNF V) :
    encode id (x++y) = encode id x ++ encode id y := by
  simp only [encode,List.map_append]

/-- The exact raw 24 external text rows parse to a contiguous block in the
actual compiled target. No numeric offset in the full target is asserted. -/
theorem parsed24_contiguous :
    ExternalPacketPilot.parseBodyChunk 37365 24 ExternalPacket24.body =
      some (encode productionId32 typedPrefix) ∧
    compile (dictionary 32 7 6) (typedRows 32 7 7 6) target32_covered =
      encode productionId32 pre ++
      (encode productionId32 typedPrefix ++ encode productionId32 post) := by
  constructor
  · exact ExternalPacket24.body_parses.trans (congrArg some packet24_exact.symm)
  · calc
      _ = encode productionId32 (typedRows 32 7 7 6) :=
        scope_encode (dictionary 32 7 6) (typedRows 32 7 7 6) target32_covered
      _ = encode productionId32 (pre ++ (typedPrefix ++ post)) :=
        congrArg (encode productionId32) typed_split
      _ = _ := by rw [encode_append,encode_append]

/-- The needed UNSAT-transport direction is external rows → internal rows.
Only the parsed chunk, not the rest of the external file, appears here. -/
theorem parsed24_mem_internal {C : NumberedCNF}
    (h : ExternalPacketPilot.parseBodyChunk 37365 24 ExternalPacket24.body = some C) :
    ∀ row ∈ C, row ∈ compile (dictionary 32 7 6) (typedRows 32 7 7 6) target32_covered := by
  have hc : C = encode productionId32 typedPrefix :=
    Option.some.inj (h.symm.trans parsed24_contiguous.1)
  rw [hc,parsed24_contiguous.2]
  exact fun row hr => List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl hr)))

#print axioms production_quartet_prefix
#print axioms packet24_exact
#print axioms parsed24_contiguous
#print axioms parsed24_mem_internal

end ES33.EndpointConcrete.Packet24

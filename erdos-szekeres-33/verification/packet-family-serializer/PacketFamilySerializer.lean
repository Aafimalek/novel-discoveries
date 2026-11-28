/- Static full packet-family serialization. No compiler has run here. -/
import OrientationRank
import ActualCoverage

namespace ES33.EndpointConcrete.PacketFamilySerializer

open ES33.Numbering
open VerificationGoals

abbrev Quad (n : Nat) := Fin n × Fin n × Fin n × Fin n

def varId (n A B : Nat) (v : Key n) : Nat := (dictionary n A B).idxOf v + 1

def typedPacket {n : Nat} : Quad n → CNF (Key n) :=
  fun (a,b,c,e) => packetRows a b c e

/-- Exact packet row and literal order via arithmetic orientation ranks. -/
def fastPacket {n : Nat} : Quad n → NumberedCNF
  | (a,b,c,e) =>
    let p : Int := OrientationRank.rank a b c
    let q : Int := OrientationRank.rank a b e
    let r : Int := OrientationRank.rank a c e
    let s : Int := OrientationRank.rank b c e
    [[-p,-s,q],[-q,-s,r],[-p,-r,q],[p,s,-q],[q,s,-r],[p,r,-q]]

def fastPacketFamily (n : Nat) : NumberedCNF :=
  (packets n).flatMap fastPacket

private theorem encode_packet {n A B : Nat} {a b c e : Fin n}
    (hab : a<b) (hbc : b<c) (hce : c<e) :
    encode (varId n A B) (packetRows a b c e) = fastPacket (a,b,c,e) := by
  have hp : varId n A B (.sign a b c) = OrientationRank.rank a b c :=
    OrientationRank.production_sign_id hab hbc
  have hq : varId n A B (.sign a b e) = OrientationRank.rank a b e :=
    OrientationRank.production_sign_id hab (Fin.lt_trans hbc hce)
  have hr : varId n A B (.sign a c e) = OrientationRank.rank a c e :=
    OrientationRank.production_sign_id (Fin.lt_trans hab hbc) hce
  have hs : varId n A B (.sign b c e) = OrientationRank.rank b c e :=
    OrientationRank.production_sign_id hbc hce
  simp [encode,packetRows,fastPacket,signed,sign,flip,hp,hq,hr,hs]

/-- Exact equality of ordered signed rows for an entire generated family. -/
theorem encode_packet_family (n A B : Nat) :
    encode (varId n A B) ((packets n).flatMap typedPacket) = fastPacketFamily n := by
  have he :
      (packets n).map (fun q => encode (varId n A B) (typedPacket q)) =
        (packets n).map fastPacket := by
    apply List.map_congr_left
    rintro ⟨a,b,c,e⟩ h
    obtain ⟨hab,hbc,hce⟩ := packet_order h
    exact encode_packet hab hbc hce
  calc
    _ = (packets n).flatMap (fun q => encode (varId n A B) (typedPacket q)) := by
      simp only [encode,List.map_flatMap]
    _ = ((packets n).map (fun q => encode (varId n A B) (typedPacket q))).flatten :=
      List.flatMap_def
    _ = _ := congrArg List.flatten he

/-- Proof attachment changes neither row order nor the signed integers. -/
theorem compile_eq_encode {V : Type} [BEq V] (keys : List V) (F : CNF V)
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

def prePacketTyped (n K A B : Nat) : CNF (Key n) :=
  sideRows n A .cap ++ sideRows n B .cup ++ crossRows n K A B

/-- The production packet family is exactly the final suffix, without
assuming a concrete offset or counting the whole CNF. -/
theorem compiled_packet_suffix {n K A B : Nat} (h : covered n K A B) :
    compile (dictionary n A B) (typedRows n K A B) h =
      encode (varId n A B) (prePacketTyped n K A B) ++ fastPacketFamily n := by
  have hd {V : Type} (id : V → Nat) (P Q : CNF V) :
      encode id (P++Q) = encode id P ++ encode id Q := by
    simp only [encode,List.map_append]
  calc
    _ = encode (varId n A B) (typedRows n K A B) :=
      compile_eq_encode (dictionary n A B) (typedRows n K A B) h
    _ = encode (varId n A B) (prePacketTyped n K A B ++ (packets n).flatMap typedPacket) :=
      rfl
    _ = _ := by rw [hd,encode_packet_family]

/-- Token interface with the actual production variable bound. -/
def packetTokenDoc (n A B : Nat) : TokenDocument :=
  TokenDocument.emit (dictionary n A B).length (fastPacketFamily n)

theorem packet_token_roundtrip {n K A B : Nat} (h : covered n K A B) :
    (packetTokenDoc n A B).parse = some (fastPacketFamily n) := by
  unfold packetTokenDoc
  apply token_document_roundtrip
  intro c hc l hl
  have hfull : c ∈ compile (dictionary n A B) (typedRows n K A B) h := by
    rw [compiled_packet_suffix h]
    exact List.mem_append.mpr (Or.inr hc)
  exact every_numbered_literal_legal (dictionary n A B) (scope _ _ h) c l hfull hl

/-- Canonical line syntax: signed decimal words, single spaces, one
terminal zero, LF. This renderer makes no external byte equality claim. -/
def renderRow (r : List Int) : String :=
  String.intercalate " " (r.map toString ++ ["0"]) ++ "\n"

def renderBody (rows : NumberedCNF) : String :=
  String.join (rows.map renderRow)

def renderPacketSuffix (n : Nat) : String :=
  renderBody (fastPacketFamily n)

theorem renderBody_append (P Q : NumberedCNF) :
    renderBody (P++Q) = renderBody P ++ renderBody Q := by
  simp only [renderBody,List.map_append,String.join_append]

/-- Internally rendered canonical bytes also factor at the packet boundary.
This is not a proposition about bytes received from a filesystem parser. -/
theorem render_compiled_suffix {n K A B : Nat} (h : covered n K A B) :
    renderBody (compile (dictionary n A B) (typedRows n K A B) h) =
      renderBody (encode (varId n A B) (prePacketTyped n K A B)) ++
        renderPacketSuffix n := by
  change _ = _ ++ renderBody (fastPacketFamily n)
  rw [compiled_packet_suffix h,renderBody_append]

/-- External-to-internal direction; the actual loader must establish the
exact packet-content premise separately for the bytes it consumes. -/
theorem packet_rows_in_compiled {n K A B : Nat} (h : covered n K A B)
    {external : NumberedCNF} (exactPacketContent : external = fastPacketFamily n) :
    ∀ c ∈ external, c ∈ compile (dictionary n A B) (typedRows n K A B) h := by
  rw [exactPacketContent,compiled_packet_suffix h]
  exact fun _ hm => List.mem_append.mpr (Or.inr hm)

#print axioms encode_packet_family
#print axioms compile_eq_encode
#print axioms compiled_packet_suffix
#print axioms packet_token_roundtrip
#print axioms render_compiled_suffix
#print axioms packet_rows_in_compiled

end ES33.EndpointConcrete.PacketFamilySerializer

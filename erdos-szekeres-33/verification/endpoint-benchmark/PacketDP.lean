import Mathlib.Data.Bool.Basic
import Mathlib.Tactic

namespace ES33.EndpointDP

/-- The six ternary implications used by Baek–Balko's etv_signotope. -/
def upstreamPacket (p q r s : Bool) : Prop :=
  ((p ∧ s) → q) ∧ ((q ∧ s) → r) ∧ ((p ∧ r) → q) ∧
  ((p = false ∧ s = false) → q = false) ∧
  ((q = false ∧ s = false) → r = false) ∧
  ((p = false ∧ r = false) → q = false)

theorem upstream_packet_iff_one_change (p q r s : Bool) :
    upstreamPacket p q r s ↔
    (p ≤ q ∧ q ≤ r ∧ r ≤ s) ∨ (s ≤ r ∧ r ≤ q ∧ q ≤ p) := by
  cases p <;> cases q <;> cases r <;> cases s <;> simp [upstreamPacket]

/-- On a legal packet, convex parity says exactly that each of the first
two signs agree and each of the last two signs agree. -/
theorem even_legal_packet_iff_pairs (p q r s : Bool)
    (h : upstreamPacket p q r s) :
    Bool.xor p (Bool.xor q (Bool.xor r s)) = false ↔ p = q ∧ r = s := by
  cases p <;> cases q <;> cases r <;> cases s <;> simp_all [upstreamPacket]

/-- Equal first and last packet signs force the two middle signs equal. -/
theorem equal_packet_ends (p q r s : Bool) (h : upstreamPacket p q r s) (e : p = s) :
    q = p ∧ r = s := by
  cases p <;> cases q <;> cases r <;> cases s <;> simp_all [upstreamPacket]

/-- Different middle signs fix both of the extreme packet signs. -/
theorem different_middle_packet (p q r s : Bool) (h : upstreamPacket p q r s) (e : q ≠ r) :
    p = q ∧ s = r := by
  cases p <;> cases q <;> cases r <;> cases s <;> simp_all [upstreamPacket]

#print axioms upstream_packet_iff_one_change
#print axioms even_legal_packet_iff_pairs
#print axioms equal_packet_ends
#print axioms different_middle_packet

end ES33.EndpointDP

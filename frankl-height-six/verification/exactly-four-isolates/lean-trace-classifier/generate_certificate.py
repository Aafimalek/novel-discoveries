"""Rebuild Lean's finite certificate data. Lean checks it independently."""
from itertools import combinations
from pathlib import Path

U = range(16)
mandatory = [n for n in U if n.bit_count() >= 3]
optional = [n for n in U if n not in mandatory]
pairs = list(combinations(range(4), 2))


def profile(m):
    return set(mandatory) | {t for i, t in enumerate(optional) if m & (1 << i)}


def weight(F, i):
    return sum(bool(t & (1 << i)) for t in F)


def eligible(F):
    return 2 * weight(F, 0) < len(F) and all(t | u in F for t in F for u in F)


def witness(F):
    safe = [t for t in U if all(t | u in F for u in F)]
    for i, j in pairs:
        avoiding = [t for t in safe if not (t & ((1 << i) | (1 << j)))]
        support = 0
        for t in avoiding:
            support |= t
        if support.bit_count() + len(F) >= weight(F, i) + weight(F, j):
            continue
        for chain in combinations(sorted(F), 4):
            if support & chain[0] != support:
                continue
            if all(a & b == a for a, b in zip(chain, chain[1:])):
                return i, j, *chain


def make():
    counts = []
    rows = []
    survivors = []
    for start in range(0, 2048, 32):
        count = 0
        for m in range(start, start + 32):
            F = profile(m)
            if eligible(F):
                count += 1
                w = witness(F)
                if w:
                    rows.append((m, w))
                else:
                    survivors.append(m)
        counts.append(count)
    assert sum(counts) == 106
    assert len(rows) == 105
    assert survivors == [2045]
    code = ["import FranklFourTraceCertificateDefinitions", "",
            "/- Generated numeric certificate. Every row is rechecked by Lean. -/",
            "namespace FranklFourTraceCertificate", "",
            "private def table : List (Nat × Witness) :=",
            "  ["]
    for m, (i, j, a, b, c, d) in rows:
        code.append(f"    ({m}, ⟨{i}, {j}, {a}, {b}, {c}, {d}⟩),")
    code[-1] = code[-1].removesuffix(",")
    code += ["  ]", "",
             "private def lookup (m : Nat) : Option Witness :=",
             "  (table.find? fun row => row.1 == m).map Prod.snd", "",
             "private def check (m : Nat) : Bool :=",
             "  if eligibleB m then",
             "    if m == 2045 then true",
             "    else (lookup m).any (validWitness m)",
             "  else true", "",
             "private structure Block (start size expected : Nat) : Prop where",
             "  passed : (List.range' start size).all check = true",
             "  count : ((List.range' start size).filter eligibleB).length = expected", "",
             "private theorem combine {s n m a b : Nat}",
             "    (left : Block s n a) (right : Block (s+n) m b) :",
             "    Block s (n+m) (a+b) := by",
             "  constructor",
             "  · rw [← List.range'_append_1, List.all_append, left.passed, right.passed]",
             "    rfl",
             "  · rw [← List.range'_append_1, List.filter_append, List.length_append,",
             "      left.count, right.count]", ""]
    for i, count in enumerate(counts):
        code += ["set_option maxRecDepth 20000 in",
                 "set_option maxHeartbeats 2000000 in",
                 f"private theorem b{i} : Block {i*32} 32 {count} := by",
                 "  constructor <;> decide", ""]
    nodes = [(f"b{i}", i*32, 32, count) for i, count in enumerate(counts)]
    level = 0
    while len(nodes) > 1:
        next_nodes = []
        for i in range(0, len(nodes), 2):
            (a, s, n, ac), (b, end, m, bc) = nodes[i:i+2]
            assert s+n == end
            name = f"join{level}_{i//2}"
            code += [f"private theorem {name} : Block {s} {n+m} {ac+bc} :=",
                     f"  combine {a} {b}", ""]
            next_nodes.append((name, s, n+m, ac+bc))
        nodes = next_nodes
        level += 1
    name = nodes[0][0]
    code += ["theorem eligible_mask_count :",
             "    ((List.range' 0 2048).filter eligibleB).length = 106 :=",
             f"  {name}.count", "",
             "theorem classified_mask (m : Nat) (hm : m < 2048)",
             "    (he : eligibleB m = true) :",
             "    m = 2045 ∨ ∃ w, validWitness m w = true := by",
             "  have hmR : m ∈ List.range' 0 2048 :=",
             "    List.mem_range'_1.mpr ⟨Nat.zero_le _, by simpa using hm⟩",
             f"  have hp := List.all_eq_true.mp {name}.passed m hmR",
             "  by_cases hs : m = 2045",
             "  · exact Or.inl hs",
             "  · have hsB : (m == 2045) = false := by simp [hs]",
             "    cases e : lookup m with",
             "    | none => simp [check, he, hsB, e] at hp",
             "    | some w =>",
             "      exact Or.inr ⟨w, by simpa [check, he, hsB, e] using hp⟩", "",
             "#print axioms eligible_mask_count",
             "#print axioms classified_mask",
             "end FranklFourTraceCertificate", ""]
    return "\n".join(code)


if __name__ == "__main__":
    here = Path(__file__).resolve().parent
    (here / "FranklFourTraceCertificates.lean").write_text(make())

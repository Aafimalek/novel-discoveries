"""Check the finite residue graph without Lean, SAT, or dependencies."""
from itertools import combinations

TABLE = """
04512123423230305
45421232303535451
04142123430350512
21234254305050121
12323035051514142
34030504514121230
03505150121212123
45354504121421430
05045121212303505
51404214323030450
12121230312503045
51212303535050402
43243230304515121
32303505451451212
03030454512413423
50303505121232312
45054214214123435
""".strip().splitlines()
P = 17
assert len(TABLE) == P
assert all(len(row) == P and set(row) <= set("012345") for row in TABLE)
assert (4**2-33) % P == (2**2-21) % P == 0
assert (2*4) % P != 0 and (2*2) % P != 0
assert not any((x*x+3) % P == 0 for x in range(P))
points = [(a, b) for b in range(P) for a in range(P)]
edges = 0
for (a, b), (c, d) in combinations(points, 2):
    if ((a-c)**2+3*(b-d)**2) % P == 1:
        assert TABLE[b][a] != TABLE[d][c], (a, b, c, d)
        edges += 1
assert edges == 2601
print(f"Checked {len(points)} vertices, {edges} unit edges, proper six-color table.")

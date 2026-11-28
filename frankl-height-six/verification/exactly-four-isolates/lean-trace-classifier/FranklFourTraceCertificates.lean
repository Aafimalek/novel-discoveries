import FranklFourTraceCertificateDefinitions

/- Generated numeric certificate. Every row is rechecked by Lean. -/
namespace FranklFourTraceCertificate

private def table : List (Nat × Witness) :=
  [
    (85, ⟨1, 2, 0, 2, 6, 7⟩),
    (581, ⟨0, 1, 0, 2, 6, 7⟩),
    (593, ⟨1, 2, 0, 4, 6, 7⟩),
    (596, ⟨0, 1, 4, 6, 7, 15⟩),
    (597, ⟨1, 2, 0, 2, 6, 7⟩),
    (605, ⟨0, 1, 4, 6, 7, 15⟩),
    (629, ⟨1, 2, 0, 2, 6, 7⟩),
    (645, ⟨1, 3, 0, 2, 7, 15⟩),
    (705, ⟨1, 2, 8, 10, 11, 15⟩),
    (708, ⟨0, 1, 8, 10, 11, 15⟩),
    (709, ⟨1, 2, 8, 10, 11, 15⟩),
    (717, ⟨0, 1, 8, 10, 11, 15⟩),
    (741, ⟨1, 2, 8, 10, 11, 15⟩),
    (853, ⟨1, 3, 4, 6, 7, 15⟩),
    (965, ⟨1, 3, 0, 2, 6, 7⟩),
    (1093, ⟨1, 2, 0, 2, 6, 7⟩),
    (1105, ⟨0, 2, 0, 4, 6, 7⟩),
    (1108, ⟨0, 2, 2, 6, 7, 15⟩),
    (1109, ⟨1, 2, 0, 2, 6, 7⟩),
    (1117, ⟨1, 2, 0, 2, 3, 7⟩),
    (1141, ⟨0, 2, 2, 6, 7, 15⟩),
    (1169, ⟨2, 3, 0, 4, 7, 15⟩),
    (1217, ⟨1, 2, 8, 12, 13, 15⟩),
    (1232, ⟨0, 2, 8, 12, 13, 15⟩),
    (1233, ⟨1, 2, 8, 12, 13, 15⟩),
    (1241, ⟨1, 2, 8, 12, 13, 15⟩),
    (1265, ⟨0, 2, 8, 12, 13, 15⟩),
    (1365, ⟨2, 3, 2, 6, 7, 15⟩),
    (1489, ⟨2, 3, 0, 4, 6, 7⟩),
    (1541, ⟨1, 2, 0, 2, 7, 15⟩),
    (1553, ⟨1, 2, 0, 4, 7, 15⟩),
    (1601, ⟨1, 2, 0, 6, 7, 15⟩),
    (1604, ⟨2, 3, 2, 6, 7, 15⟩),
    (1605, ⟨1, 2, 0, 2, 6, 7⟩),
    (1613, ⟨1, 2, 0, 2, 3, 7⟩),
    (1616, ⟨1, 3, 4, 6, 7, 15⟩),
    (1617, ⟨1, 2, 0, 4, 6, 7⟩),
    (1620, ⟨1, 3, 4, 6, 7, 15⟩),
    (1621, ⟨1, 2, 0, 2, 6, 7⟩),
    (1625, ⟨1, 2, 0, 3, 7, 15⟩),
    (1628, ⟨1, 3, 4, 6, 7, 15⟩),
    (1629, ⟨1, 2, 0, 2, 3, 7⟩),
    (1637, ⟨1, 2, 0, 2, 6, 7⟩),
    (1649, ⟨1, 2, 0, 4, 5, 7⟩),
    (1652, ⟨2, 3, 2, 6, 7, 15⟩),
    (1653, ⟨1, 2, 0, 2, 6, 7⟩),
    (1661, ⟨1, 2, 0, 2, 3, 7⟩),
    (1665, ⟨0, 3, 0, 8, 10, 11⟩),
    (1668, ⟨0, 3, 2, 10, 11, 15⟩),
    (1669, ⟨1, 3, 0, 2, 7, 15⟩),
    (1677, ⟨1, 3, 0, 2, 3, 7⟩),
    (1680, ⟨0, 3, 4, 12, 13, 15⟩),
    (1681, ⟨1, 3, 4, 12, 13, 15⟩),
    (1689, ⟨1, 3, 4, 12, 13, 15⟩),
    (1701, ⟨2, 3, 2, 10, 11, 15⟩),
    (1713, ⟨2, 3, 0, 4, 5, 7⟩),
    (1728, ⟨1, 2, 8, 10, 11, 15⟩),
    (1729, ⟨1, 2, 8, 10, 11, 15⟩),
    (1732, ⟨1, 2, 8, 10, 11, 15⟩),
    (1733, ⟨1, 2, 8, 10, 11, 15⟩),
    (1737, ⟨1, 2, 8, 10, 11, 15⟩),
    (1740, ⟨1, 2, 8, 10, 11, 15⟩),
    (1741, ⟨1, 2, 8, 10, 11, 15⟩),
    (1744, ⟨1, 2, 8, 10, 11, 15⟩),
    (1745, ⟨1, 2, 8, 10, 11, 15⟩),
    (1748, ⟨1, 2, 8, 10, 11, 15⟩),
    (1749, ⟨1, 2, 8, 10, 11, 15⟩),
    (1752, ⟨1, 2, 8, 10, 11, 15⟩),
    (1753, ⟨1, 2, 8, 10, 11, 15⟩),
    (1756, ⟨1, 2, 8, 10, 11, 15⟩),
    (1757, ⟨1, 2, 8, 10, 11, 15⟩),
    (1761, ⟨1, 2, 8, 10, 11, 15⟩),
    (1764, ⟨1, 2, 8, 10, 11, 15⟩),
    (1765, ⟨1, 2, 8, 10, 11, 15⟩),
    (1773, ⟨1, 2, 8, 10, 11, 15⟩),
    (1776, ⟨1, 2, 8, 10, 11, 15⟩),
    (1777, ⟨1, 2, 8, 10, 11, 15⟩),
    (1780, ⟨1, 2, 8, 10, 11, 15⟩),
    (1781, ⟨1, 2, 8, 10, 11, 15⟩),
    (1785, ⟨1, 2, 8, 10, 11, 15⟩),
    (1788, ⟨1, 2, 8, 10, 11, 15⟩),
    (1789, ⟨1, 2, 8, 10, 11, 15⟩),
    (1861, ⟨1, 3, 0, 2, 6, 7⟩),
    (1873, ⟨1, 3, 4, 6, 7, 15⟩),
    (1876, ⟨1, 3, 4, 6, 7, 15⟩),
    (1877, ⟨1, 3, 4, 6, 7, 15⟩),
    (1885, ⟨1, 3, 4, 6, 7, 15⟩),
    (1909, ⟨2, 3, 2, 6, 7, 15⟩),
    (1925, ⟨0, 3, 2, 10, 11, 15⟩),
    (1937, ⟨0, 3, 4, 12, 13, 15⟩),
    (1985, ⟨1, 3, 0, 6, 7, 15⟩),
    (1988, ⟨2, 3, 2, 6, 7, 15⟩),
    (1989, ⟨1, 3, 0, 2, 6, 7⟩),
    (1997, ⟨1, 3, 0, 2, 3, 7⟩),
    (2000, ⟨1, 3, 4, 6, 7, 15⟩),
    (2001, ⟨1, 3, 4, 6, 7, 15⟩),
    (2004, ⟨1, 3, 4, 6, 7, 15⟩),
    (2005, ⟨1, 3, 4, 6, 7, 15⟩),
    (2009, ⟨1, 3, 4, 6, 7, 15⟩),
    (2012, ⟨1, 3, 4, 6, 7, 15⟩),
    (2013, ⟨1, 3, 4, 6, 7, 15⟩),
    (2021, ⟨2, 3, 2, 6, 7, 15⟩),
    (2033, ⟨2, 3, 0, 4, 5, 7⟩),
    (2036, ⟨2, 3, 2, 6, 7, 15⟩),
    (2037, ⟨2, 3, 2, 6, 7, 15⟩)
  ]

private def lookup (m : Nat) : Option Witness :=
  (table.find? fun row => row.1 == m).map Prod.snd

private def check (m : Nat) : Bool :=
  if eligibleB m then
    if m == 2045 then true
    else (lookup m).any (validWitness m)
  else true

private structure Block (start size expected : Nat) : Prop where
  passed : (List.range' start size).all check = true
  count : ((List.range' start size).filter eligibleB).length = expected

private theorem combine {s n m a b : Nat}
    (left : Block s n a) (right : Block (s+n) m b) :
    Block s (n+m) (a+b) := by
  constructor
  · rw [← List.range'_append_1, List.all_append, left.passed, right.passed]
    rfl
  · rw [← List.range'_append_1, List.filter_append, List.length_append,
      left.count, right.count]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem b0 : Block 0 32 0 := by
  constructor <;> decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem b1 : Block 32 32 0 := by
  constructor <;> decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem b2 : Block 64 32 1 := by
  constructor <;> decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem b3 : Block 96 32 0 := by
  constructor <;> decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem b4 : Block 128 32 0 := by
  constructor <;> decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem b5 : Block 160 32 0 := by
  constructor <;> decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem b6 : Block 192 32 0 := by
  constructor <;> decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem b7 : Block 224 32 0 := by
  constructor <;> decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem b8 : Block 256 32 0 := by
  constructor <;> decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem b9 : Block 288 32 0 := by
  constructor <;> decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem b10 : Block 320 32 0 := by
  constructor <;> decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem b11 : Block 352 32 0 := by
  constructor <;> decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem b12 : Block 384 32 0 := by
  constructor <;> decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem b13 : Block 416 32 0 := by
  constructor <;> decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem b14 : Block 448 32 0 := by
  constructor <;> decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem b15 : Block 480 32 0 := by
  constructor <;> decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem b16 : Block 512 32 0 := by
  constructor <;> decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem b17 : Block 544 32 0 := by
  constructor <;> decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem b18 : Block 576 32 5 := by
  constructor <;> decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem b19 : Block 608 32 1 := by
  constructor <;> decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem b20 : Block 640 32 1 := by
  constructor <;> decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem b21 : Block 672 32 0 := by
  constructor <;> decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem b22 : Block 704 32 4 := by
  constructor <;> decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem b23 : Block 736 32 1 := by
  constructor <;> decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem b24 : Block 768 32 0 := by
  constructor <;> decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem b25 : Block 800 32 0 := by
  constructor <;> decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem b26 : Block 832 32 1 := by
  constructor <;> decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem b27 : Block 864 32 0 := by
  constructor <;> decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem b28 : Block 896 32 0 := by
  constructor <;> decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem b29 : Block 928 32 0 := by
  constructor <;> decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem b30 : Block 960 32 1 := by
  constructor <;> decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem b31 : Block 992 32 0 := by
  constructor <;> decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem b32 : Block 1024 32 0 := by
  constructor <;> decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem b33 : Block 1056 32 0 := by
  constructor <;> decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem b34 : Block 1088 32 5 := by
  constructor <;> decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem b35 : Block 1120 32 1 := by
  constructor <;> decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem b36 : Block 1152 32 1 := by
  constructor <;> decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem b37 : Block 1184 32 0 := by
  constructor <;> decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem b38 : Block 1216 32 4 := by
  constructor <;> decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem b39 : Block 1248 32 1 := by
  constructor <;> decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem b40 : Block 1280 32 0 := by
  constructor <;> decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem b41 : Block 1312 32 0 := by
  constructor <;> decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem b42 : Block 1344 32 1 := by
  constructor <;> decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem b43 : Block 1376 32 0 := by
  constructor <;> decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem b44 : Block 1408 32 0 := by
  constructor <;> decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem b45 : Block 1440 32 0 := by
  constructor <;> decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem b46 : Block 1472 32 1 := by
  constructor <;> decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem b47 : Block 1504 32 0 := by
  constructor <;> decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem b48 : Block 1536 32 2 := by
  constructor <;> decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem b49 : Block 1568 32 0 := by
  constructor <;> decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem b50 : Block 1600 32 11 := by
  constructor <;> decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem b51 : Block 1632 32 5 := by
  constructor <;> decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem b52 : Block 1664 32 7 := by
  constructor <;> decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem b53 : Block 1696 32 2 := by
  constructor <;> decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem b54 : Block 1728 32 15 := by
  constructor <;> decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem b55 : Block 1760 32 11 := by
  constructor <;> decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem b56 : Block 1792 32 0 := by
  constructor <;> decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem b57 : Block 1824 32 0 := by
  constructor <;> decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem b58 : Block 1856 32 5 := by
  constructor <;> decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem b59 : Block 1888 32 1 := by
  constructor <;> decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem b60 : Block 1920 32 2 := by
  constructor <;> decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem b61 : Block 1952 32 0 := by
  constructor <;> decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem b62 : Block 1984 32 11 := by
  constructor <;> decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
private theorem b63 : Block 2016 32 5 := by
  constructor <;> decide

private theorem join0_0 : Block 0 64 0 :=
  combine b0 b1

private theorem join0_1 : Block 64 64 1 :=
  combine b2 b3

private theorem join0_2 : Block 128 64 0 :=
  combine b4 b5

private theorem join0_3 : Block 192 64 0 :=
  combine b6 b7

private theorem join0_4 : Block 256 64 0 :=
  combine b8 b9

private theorem join0_5 : Block 320 64 0 :=
  combine b10 b11

private theorem join0_6 : Block 384 64 0 :=
  combine b12 b13

private theorem join0_7 : Block 448 64 0 :=
  combine b14 b15

private theorem join0_8 : Block 512 64 0 :=
  combine b16 b17

private theorem join0_9 : Block 576 64 6 :=
  combine b18 b19

private theorem join0_10 : Block 640 64 1 :=
  combine b20 b21

private theorem join0_11 : Block 704 64 5 :=
  combine b22 b23

private theorem join0_12 : Block 768 64 0 :=
  combine b24 b25

private theorem join0_13 : Block 832 64 1 :=
  combine b26 b27

private theorem join0_14 : Block 896 64 0 :=
  combine b28 b29

private theorem join0_15 : Block 960 64 1 :=
  combine b30 b31

private theorem join0_16 : Block 1024 64 0 :=
  combine b32 b33

private theorem join0_17 : Block 1088 64 6 :=
  combine b34 b35

private theorem join0_18 : Block 1152 64 1 :=
  combine b36 b37

private theorem join0_19 : Block 1216 64 5 :=
  combine b38 b39

private theorem join0_20 : Block 1280 64 0 :=
  combine b40 b41

private theorem join0_21 : Block 1344 64 1 :=
  combine b42 b43

private theorem join0_22 : Block 1408 64 0 :=
  combine b44 b45

private theorem join0_23 : Block 1472 64 1 :=
  combine b46 b47

private theorem join0_24 : Block 1536 64 2 :=
  combine b48 b49

private theorem join0_25 : Block 1600 64 16 :=
  combine b50 b51

private theorem join0_26 : Block 1664 64 9 :=
  combine b52 b53

private theorem join0_27 : Block 1728 64 26 :=
  combine b54 b55

private theorem join0_28 : Block 1792 64 0 :=
  combine b56 b57

private theorem join0_29 : Block 1856 64 6 :=
  combine b58 b59

private theorem join0_30 : Block 1920 64 2 :=
  combine b60 b61

private theorem join0_31 : Block 1984 64 16 :=
  combine b62 b63

private theorem join1_0 : Block 0 128 1 :=
  combine join0_0 join0_1

private theorem join1_1 : Block 128 128 0 :=
  combine join0_2 join0_3

private theorem join1_2 : Block 256 128 0 :=
  combine join0_4 join0_5

private theorem join1_3 : Block 384 128 0 :=
  combine join0_6 join0_7

private theorem join1_4 : Block 512 128 6 :=
  combine join0_8 join0_9

private theorem join1_5 : Block 640 128 6 :=
  combine join0_10 join0_11

private theorem join1_6 : Block 768 128 1 :=
  combine join0_12 join0_13

private theorem join1_7 : Block 896 128 1 :=
  combine join0_14 join0_15

private theorem join1_8 : Block 1024 128 6 :=
  combine join0_16 join0_17

private theorem join1_9 : Block 1152 128 6 :=
  combine join0_18 join0_19

private theorem join1_10 : Block 1280 128 1 :=
  combine join0_20 join0_21

private theorem join1_11 : Block 1408 128 1 :=
  combine join0_22 join0_23

private theorem join1_12 : Block 1536 128 18 :=
  combine join0_24 join0_25

private theorem join1_13 : Block 1664 128 35 :=
  combine join0_26 join0_27

private theorem join1_14 : Block 1792 128 6 :=
  combine join0_28 join0_29

private theorem join1_15 : Block 1920 128 18 :=
  combine join0_30 join0_31

private theorem join2_0 : Block 0 256 1 :=
  combine join1_0 join1_1

private theorem join2_1 : Block 256 256 0 :=
  combine join1_2 join1_3

private theorem join2_2 : Block 512 256 12 :=
  combine join1_4 join1_5

private theorem join2_3 : Block 768 256 2 :=
  combine join1_6 join1_7

private theorem join2_4 : Block 1024 256 12 :=
  combine join1_8 join1_9

private theorem join2_5 : Block 1280 256 2 :=
  combine join1_10 join1_11

private theorem join2_6 : Block 1536 256 53 :=
  combine join1_12 join1_13

private theorem join2_7 : Block 1792 256 24 :=
  combine join1_14 join1_15

private theorem join3_0 : Block 0 512 1 :=
  combine join2_0 join2_1

private theorem join3_1 : Block 512 512 14 :=
  combine join2_2 join2_3

private theorem join3_2 : Block 1024 512 14 :=
  combine join2_4 join2_5

private theorem join3_3 : Block 1536 512 77 :=
  combine join2_6 join2_7

private theorem join4_0 : Block 0 1024 15 :=
  combine join3_0 join3_1

private theorem join4_1 : Block 1024 1024 91 :=
  combine join3_2 join3_3

private theorem join5_0 : Block 0 2048 106 :=
  combine join4_0 join4_1

theorem eligible_mask_count :
    ((List.range' 0 2048).filter eligibleB).length = 106 :=
  join5_0.count

theorem classified_mask (m : Nat) (hm : m < 2048)
    (he : eligibleB m = true) :
    m = 2045 ∨ ∃ w, validWitness m w = true := by
  have hmR : m ∈ List.range' 0 2048 :=
    List.mem_range'_1.mpr ⟨Nat.zero_le _, by simpa using hm⟩
  have hp := List.all_eq_true.mp join5_0.passed m hmR
  by_cases hs : m = 2045
  · exact Or.inl hs
  · have hsB : (m == 2045) = false := by simp [hs]
    cases e : lookup m with
    | none => simp [check, he, hsB, e] at hp
    | some w =>
      exact Or.inr ⟨w, by simpa [check, he, hsB, e] using hp⟩

#print axioms eligible_mask_count
#print axioms classified_mask
end FranklFourTraceCertificate

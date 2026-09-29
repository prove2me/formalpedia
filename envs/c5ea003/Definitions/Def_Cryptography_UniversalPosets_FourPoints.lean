-- Prove2me | Definitions.Def_Cryptography_UniversalPosets_FourPoints
-- name    : Cryptography_UniversalPosets_FourPoints
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:29:15.570399+00:00
-- url     : https://prove2.me/theorems/c4aab550-dd83-4963-9bce-fedc0b6869c5
-- title:
--   Aether Catalog definitions — Cryptography_UniversalPosets_FourPoints
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.UniversalPosets.FourPoints`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/UniversalPosets/FourPoints.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Cryptography_UniversalPosets_StrictMono

/-!
# Four points: `U(4) ≤ 8`

`ExactSmall.lean` proved `U(3) = 5` and the general bound `2n - 1 ≤ U(n)`, which
gives `7 ≤ U(4)`.  This file adds the matching upper bound `U(4) ≤ 8` by
exhibiting an explicit eight-point host and *kernel-checking* that every one of
the `219` partial orders on four points embeds into it as an induced subposet.
Hence

`7 ≤ U(4) ≤ 8`.

## How the verification is organised

Deciding a statement quantified over the function type `Fin 4 → Fin 4 → Bool`
is hopeless for the kernel (the `Fintype` instance for a function type builds a
`Finset` of `65536` functions with quadratic deduplication).  Instead:

* a partial order on `Fin 4` is encoded by the `12` bits of its off-diagonal
  entries, i.e. by a natural number `m < 4096` (`relOf`, `idx4`, `pr4`);
* the embedding of the poset coded by `m` is *precomputed*: `emb4Of m` looks the
  witness up in the table `tbl4` (found by an external search, but re-verified
  here — nothing is trusted about the way the table was produced);
* the verification `host4_universal_chunk` is a single `decide +kernel` over
  `m = 64a + b` with `a, b < 64`, which keeps the kernel's recursion depth low;
* `Nat.ofBits` turns an arbitrary partial order on `Fin 4` back into a code, so
  the abstract statement `IsUniversalPosetOfSize 8 4` follows.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer).  The values `U(1), U(2), U(3) = 1, 3, 5` and the bound
`2n-1 ≤ U(n)` suggest `U(n) = 2n - 1`; the first test is `n = 4`.

Experiment (Experimenter).  An exhaustive search over the `96428` naturally
labelled seven-point posets found **no** seven-point host for the four-element
posets, while a randomised search found eight-point hosts; the sparsest one
found is the host `host4Le` used here.  The upper bound `U(4) ≤ 8` is proved
below; the lower bound `U(4) ≥ 8` (i.e. the nonexistence part) is *not* claimed
as a theorem, since replaying that search inside the kernel is infeasible.

Analysis (Analyst).  So `U(4) ∈ {7, 8}`, with computational evidence for `8`.
This already falsifies the naive guess `U(n) = 2n-1` if the evidence is correct,
and it is the first place where the structural bound stops being sharp.

Critique (Critic).  The `decide +kernel` call is a genuine finite verification
(no `native_decide`): it checks all `4096` codes, filters the `219` that are
partial orders, and verifies the tabulated embedding for each of them.  The
bridge from `IsUniversalPosetOfSize` to the coded statement is proved, not
assumed, so a wrong table would make the file fail to compile.
-/

namespace UniversalPosets

/-! ## The eight-point host -/

/-- Row `i` of the host order, as a bit mask: bit `j` is set iff `i ≤ j`.
The host is the eight-point poset found by the search described above. -/
def row4 : Fin 8 → Nat
  | 0 => 251 | 1 => 226 | 2 => 132 | 3 => 232 | 4 => 80 | 5 => 96 | 6 => 64 | 7 => 128

/-- The order relation of the eight-point host. -/
def host4Le (i j : Fin 8) : Bool := (row4 i).testBit j.val




/-! ## Coding partial orders on four points by twelve bits -/

/-- The bit position holding the entry `(i, j)`, for `i ≠ j`. -/
def idx4 : Fin 4 → Fin 4 → Nat
  | 0, 1 => 0 | 0, 2 => 1 | 0, 3 => 2 | 1, 0 => 3 | 1, 2 => 4 | 1, 3 => 5
  | 2, 0 => 6 | 2, 1 => 7 | 2, 3 => 8 | 3, 0 => 9 | 3, 1 => 10 | 3, 2 => 11
  | _, _ => 12

/-- The pair of points controlled by a given bit position; inverse to `idx4`. -/
def pr4 : Fin 12 → Fin 4 × Fin 4
  | 0 => (0, 1) | 1 => (0, 2) | 2 => (0, 3) | 3 => (1, 0) | 4 => (1, 2) | 5 => (1, 3)
  | 6 => (2, 0) | 7 => (2, 1) | 8 => (2, 3) | 9 => (3, 0) | 10 => (3, 1) | 11 => (3, 2)

/-- The relation on `Fin 4` coded by the number `m` (the diagonal is always true). -/
def relOf (m : Nat) (i j : Fin 4) : Bool := (i == j) || m.testBit (idx4 i j)

/-- The map `Fin 4 → Fin 8` coded by the number `e` in base `8`. -/
def emb4 (e : Nat) (i : Fin 4) : Fin 8 := ⟨(e / 8 ^ i.val) % 8, Nat.mod_lt _ (by norm_num)⟩

/-- `m` codes a partial order. -/
def isPO4 (m : Nat) : Prop :=
  (∀ i j k : Fin 4, relOf m i j = true → relOf m j k = true → relOf m i k = true) ∧
  (∀ i j : Fin 4, relOf m i j = true → relOf m j i = true → i = j)

instance decidableIsPO4 : DecidablePred isPO4 := fun m =>
  inferInstanceAs (Decidable ((∀ i j k : Fin 4, relOf m i j = true → relOf m j k = true →
    relOf m i k = true) ∧ (∀ i j : Fin 4, relOf m i j = true → relOf m j i = true → i = j)))

/-- Tabulated embeddings: for each of the `219` codes of a partial order on four
points, a code of an induced embedding into the host. -/
def tbl4 : List (Nat × Nat) :=
  [
    (0, 668), (1, 1321), (2, 1377), (3, 1112), (4, 2721), (5, 664), (6, 720), (7, 736),
    (8, 1293), (16, 1356), (18, 1355), (19, 1352), (20, 3540), (22, 2512), (23, 2376),
    (24, 1091), (26, 1345), (32, 2700), (34, 3554), (36, 2699), (37, 2696), (38, 3553),
    (39, 2824), (40, 643), (44, 2689), (48, 706), (50, 2498), (52, 3532), (54, 3019),
    (55, 3016), (56, 708), (58, 2369), (60, 2817), (62, 3009), (64, 1125), (72, 1117),
    (88, 1093), (96, 3239), (104, 2183), (120, 2117), (128, 1132), (129, 1131), (131, 1128),
    (132, 3260), (133, 2232), (135, 2152), (192, 1035), (193, 1065), (200, 1037),
    (256, 2644), (257, 3386), (260, 2643), (261, 3385), (262, 2640), (263, 2656),
    (264, 3351), (288, 2650), (292, 3164), (293, 3369), (294, 3425), (295, 2648),
    (296, 3343), (300, 3341), (304, 2626), (308, 3404), (310, 3403), (311, 3400),
    (312, 2628), (316, 2627), (318, 3393), (320, 531), (324, 2577), (328, 2071), (352, 3175),
    (356, 3173), (360, 2655), (364, 3165), (376, 2631), (380, 3141), (384, 538), (385, 2106),
    (388, 3196), (389, 2683), (391, 2680), (416, 2570), (420, 3180), (421, 3179),
    (423, 3176), (448, 540), (449, 2089), (452, 2593), (453, 2617), (456, 2061), (480, 2572),
    (484, 2571), (485, 3113), (488, 2575), (492, 3085), (512, 677), (520, 669), (528, 1447),
    (536, 1287), (552, 645), (568, 773), (576, 679), (584, 671), (600, 1095), (616, 647),
    (632, 709), (640, 1335), (704, 1063), (712, 1039), (832, 533), (840, 535), (872, 2654),
    (888, 2630), (960, 549), (968, 541), (1000, 2574), (1024, 684), (1025, 683),
    (1026, 1468), (1027, 1336), (1029, 680), (1031, 808), (1088, 1342), (1152, 700),
    (1153, 699), (1155, 1144), (1157, 696), (1159, 744), (1216, 1084), (1217, 1081),
    (1408, 554), (1409, 570), (1413, 2675), (1415, 2672), (1472, 556), (1473, 555),
    (1477, 2609), (1536, 139), (1537, 169), (1544, 141), (1600, 167), (1608, 143),
    (1664, 188), (1665, 185), (1728, 751), (1729, 757), (1736, 750), (1984, 559),
    (1985, 565), (1992, 558), (2048, 852), (2049, 1524), (2050, 851), (2051, 1504),
    (2054, 848), (2055, 864), (2056, 1510), (2064, 858), (2066, 924), (2067, 1480),
    (2070, 976), (2071, 856), (2072, 1476), (2074, 1473), (2096, 834), (2098, 962),
    (2102, 2955), (2103, 2952), (2104, 836), (2106, 835), (2110, 2945), (2560, 83),
    (2562, 337), (2568, 279), (2576, 468), (2578, 465), (2584, 863), (2586, 925),
    (2616, 839), (2618, 901), (2624, 85), (2632, 87), (2648, 862), (2680, 838), (3072, 90),
    (3073, 314), (3074, 482), (3075, 891), (3079, 888), (3088, 330), (3090, 458),
    (3091, 939), (3095, 936), (3200, 106), (3201, 122), (3203, 883), (3207, 880), (3584, 92),
    (3585, 297), (3586, 353), (3587, 377), (3592, 269), (3600, 332), (3602, 331),
    (3603, 425), (3608, 335), (3610, 397), (3648, 101), (3656, 93), (3672, 334), (3712, 108),
    (3713, 107), (3715, 369), (3776, 111), (3777, 117), (3784, 110)
  ]

/-- The tabulated embedding code of the poset coded by `m`. -/
def emb4Of (m : Nat) : Nat := ((tbl4.find? (fun p => p.1 == m)).map Prod.snd).getD 0

/-! ## The kernel verification -/



/-! ## From codes back to abstract posets -/




end UniversalPosets



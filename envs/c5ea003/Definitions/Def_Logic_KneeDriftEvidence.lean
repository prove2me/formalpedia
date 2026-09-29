-- Prove2me | Definitions.Def_Logic_KneeDriftEvidence
-- name    : Logic_KneeDriftEvidence
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T13:56:00.683632+00:00
-- url     : https://prove2.me/theorems/3bb7e1cd-4d73-450f-a7d2-2541634366e7
-- title:
--   Aether Catalog definitions — Logic_KneeDriftEvidence
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.KneeDriftEvidence`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/KneeDriftEvidence.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Logic_KneeFluctuationEvidence
/-
# Machine-checked arithmetic of the NET-46 sweep (computational evidence)

Exact rational recomputation of every number the NET-46 round reports at
`(d = 4, ctx = 2048)`, in the style of `Logic.KneeFluctuationEvidence`: the sweep is a
list of `(budget, retained accuracy)` pairs over `ℚ`, the knee is the first budget
reaching the bar, and every claim below is checked by `norm_num` on exact rationals
rather than read off a plot.

Recomputed here:

* the seed-2 knee `224` and the seed-1 knee `256` at `16×` (`knee_2048_s2`, `knee_2048_s1`);
* the margin `+0.002` at `224` and the deficit `0.002` at `192` — the round's own
  resolution (`margin_224`, `deficit_192`);
* the fact that the seed-1 deficit at `224` is `0.004`, **smaller than the measured
  inter-seed spread `0.006`**, so shifting the seed-1 sweep by the spread already reports
  `224` (`deficit_s1_224_lt_spread`, `knee_2048_s1_shifted`);
* the seed-2 curve dominating the seed-1 curve at both recorded budgets
  (`s2_dominates_s1`);
* the amplitude windows `(8, 12]`, `(12, 14]`, `(12, 16]`, `(14, 16]` of the four
  measured rungs and their intersection pattern (`amplitude_windows_rational`);
* the `k = 1024` loss gap `0.0006`, cleaner than seed 1's `0.0015` (`loss_gaps`).
-/


namespace KneeDriftEvidence

open KneeEvidence

/-- The measured seed-2 sweep at `(d = 4, ctx = 2048)` (NET-46), budgets increasing. -/
def sweep2048S2 : List (ℕ × ℚ) :=
  [(96, 956 / 1000), (128, 965 / 1000), (160, 971 / 1000), (192, 978 / 1000),
   (224, 982 / 1000), (256, 986 / 1000), (288, 987 / 1000), (384, 992 / 1000),
   (512, 993 / 1000), (768, 998 / 1000), (1024, 998 / 1000)]

/-- The recorded seed-1 values at the same cell (NET-45). -/
def sweep2048S1 : List (ℕ × ℚ) :=
  [(96, 939 / 1000), (224, 976 / 1000), (256, 986 / 1000)]

/-- The inter-seed spread at the deciding budget `224`: `0.982 - 0.976`. -/
def spread46Q : ℚ := 6 / 1000












end KneeDriftEvidence



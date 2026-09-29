-- Prove2me | Definitions.Def_Logic_KneeMarginChainEvidence
-- name    : Logic_KneeMarginChainEvidence
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T13:56:19.065989+00:00
-- url     : https://prove2.me/theorems/5e6d7d4c-f993-4a8f-acae-6d935a3b7583
-- title:
--   Aether Catalog definitions — Logic_KneeMarginChainEvidence
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.KneeMarginChainEvidence`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/KneeMarginChainEvidence.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Logic_KneeFluctuationEvidence
/-
# Machine-checked arithmetic of the NET-45 sweep (computational evidence)

Exact rational recomputation of every number the NET-45 round reports at
`(d = 4, ctx = 2048, seed 1)`, in the style of `Logic.KneeFluctuationEvidence` and
`Logic.KneeDriftEvidence`: the sweep is a list of `(budget, retained accuracy)` pairs over
`ℚ`, the knee is the first budget reaching the bar, and every claim is checked by
`norm_num` on exact rationals — never `native_decide`.

Recomputed here:

* the full eleven-point seed-1 sweep and its knee `256` (`knee_net45`);
* the margin `+0.0013` at the knee and the deficit `0.004` at the preceding grid point
  (`margin_256`, `deficit_224`), and the fact that this margin is the tightest of the
  five-doubling chain (`margin_chain_min`);
* the **non-monotonicity** of the measured curve at `(512, 768)` (`curve_dips`), the first
  such dip in the programme;
* the collapse of the certified prefix of the chain as the noise grows
  (`prefix_min_margins`): five doublings at `0.0013`, four at `0.002`, two at `0.004` and
  at the inter-seed spread `0.006`, none at the NET-44 spread `0.010`;
* the fact that shifting the seed-1 sweep up by the inter-seed spread `0.006` already
  reports `224` (`knee_net45_shifted`) — the NET-46 seed-2 reading is inside the seed-1
  noise;
* the effective-support doubling ratio `1.808…` (`support_ratio`);
* the deployment arithmetic `2048/256 = 8` and `2048/224 = 64/7 ≈ 9.14 ≠ 10.3`
  (`speedups_rational`).
-/


namespace KneeMarginEvidence

open KneeEvidence

/-- The full measured seed-1 sweep at `(d = 4, ctx = 2048)` (NET-45), budgets increasing. -/
def sweepNet45 : List (ℕ × ℚ) :=
  [(96, 939 / 1000), (128, 951 / 1000), (160, 963 / 1000), (192, 970 / 1000),
   (224, 976 / 1000), (256, 9813 / 10000), (288, 984 / 1000), (384, 993 / 1000),
   (512, 997 / 1000), (768, 996 / 1000), (1024, 998 / 1000)]

/-- The inter-seed spread later measured at this cell (NET-46). -/
def spread45 : ℚ := 6 / 1000

/-- The five recorded margins of the seed-1 chain, rungs `ctx = 128 … 2048`. -/
def marginChain : List ℚ := [7 / 1000, 10 / 1000, 3 / 1000, 6 / 1000, 13 / 10000]












end KneeMarginEvidence



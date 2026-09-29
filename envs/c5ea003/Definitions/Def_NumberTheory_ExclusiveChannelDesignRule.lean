-- Prove2me | Definitions.Def_NumberTheory_ExclusiveChannelDesignRule
-- name    : NumberTheory_ExclusiveChannelDesignRule
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:08:44.733101+00:00
-- url     : https://prove2.me/theorems/afb85fb7-bbf5-47f6-ac4a-d2dac0578c1a
-- title:
--   Aether Catalog definitions — NumberTheory_ExclusiveChannelDesignRule
-- statement:
--   Definition bundle for the Aether Catalog module `NumberTheory.ExclusiveChannelDesignRule`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from NumberTheory/ExclusiveChannelDesignRule.lean by skeleton subtraction
import Mathlib
import Definitions.Def_NumberTheory_ExclusiveChannelPopulation
/-
# NET-30 / Catalog·NumberTheory — The ≥2 / ≥3 design rule, derived

Second research cycle.  The first three files show *that* the measured k = 2
signature needs at least two exclusive coordinates and a strictly concave
(saturating) read-out.  This file shows that once one accepts the canonical
saturating channel — `k` exclusive coordinates of equal gain `g > 0`, summed,
rectified and clipped at the level `1` needed by the digit read-out — the whole
NET-29/NET-30 width ladder is *forced arithmetic*:

| intervention   | surviving block gain | saturated iff |
|----------------|----------------------|---------------|
| `ctl`          | `k · g`              | `k g ≥ 1`     |
| `zeroAt i`     | `(k-1) · g`          | `(k-1) g ≥ 1` |
| `flipAt i`     | `(k-2) · g`          | `(k-2) g ≥ 1` |
| `zeroAll`      | `0`                  | never         |

At unit gain this reads: single ablations are no-ops **iff `k ≥ 2`**, sign flips
are no-ops **iff `k ≥ 3`**, and the whole block is never dispensable.  That is
exactly the empirical ladder:

* `k = 1`: ablation = block ablation, no redundancy (Part B);
* `k = 2`: single ablations no-op, **flip breaks** (`0.9980 → 0.7505`, NET-30);
* `k = 3`: single ablations no-op **and flip no-ops** (NET-29's "signs never
  matter", which NET-30 correctly downgraded to a `k = 3` statement).

Main results: `satGate_uniform`, `satGate_uniform_zeroAt`,
`satGate_uniform_flipAt` (the table), `self_sufficient_iff_gain`,
`sign_robust_iff_gain` (the two design thresholds),
`design_rule_two_exclusive_dims`, `design_rule_three_for_sign_robustness`
(the unit-gain corollaries — NET-30's design rule, derived rather than fitted),
and `saturation_ladder_k_one_two_three`, which packages the three measured
widths in one statement.

`self_sufficiency_monotone_in_gain` records the model's falsifiable prediction
in the other direction: at fixed width and fixed clip level, *larger* exclusive
coordinates are *more* self-sufficient.  The measured s = 13 arms are the
opposite (largest coordinates of their width, least self-sufficient), so a
fixed clip level is refuted for that seed and the clip must co-scale with the
coordinate magnitude — the sharpest next-cycle test this round produces.
-/


namespace NumberTheory.ExclusiveChannel

open Finset

variable {k : ℕ}

/-! ## Block sums under the interventions -/



/-! ## The canonical saturating channel -/

/-- `k` exclusive coordinates of equal gain `g`. -/
def uniformCoef (k : ℕ) (g : ℝ) : Fin k → ℝ := fun _ => g





/-! ## The two design thresholds -/



/-! ## The unit-gain ladder: NET-30's design rule, derived -/




/-! ## A falsifiable prediction in the other direction -/


end NumberTheory.ExclusiveChannel



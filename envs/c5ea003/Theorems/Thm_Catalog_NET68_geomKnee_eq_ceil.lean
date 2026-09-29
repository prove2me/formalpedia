-- Prove2me | Theorems.Thm_Catalog_NET68_geomKnee_eq_ceil
-- name    : Catalog.NET68.geomKnee_eq_ceil
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:26:55.005485+00:00
-- url     : https://prove2.me/theorems/7a876083-772f-44bc-95c8-3011c3b63660
-- title:
--   The continuous knee.
-- statement:
--   **The continuous knee.**  For a decay rate `r ∈ (0,1)` and residual tolerance
--   `ρ ∈ (0,1)`, the geometric knee is exactly `⌈log ρ / log r⌉₊`.  This is the quantity the
--   budget law is really about; the measured `k*` is its ceiling on the fine grid.
--
--   ```lean
--   theorem Catalog.NET68.geomKnee_eq_ceil{r ρ : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hρ0 : 0 < ρ) :
--       geomKnee r ρ = ⌈Real.log ρ / Real.log r⌉₊ := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/NET68DecayRescalingAlternative.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/NET68DecayRescalingAlternative.lean#L51

-- Thm stub generated from Applications/NET68DecayRescalingAlternative.lean
import Mathlib
import Definitions.Def_Applications_NET68DecayRescalingAlternative
import Definitions.Def_Applications_NET68DomainJumpBudgetLaw
/-
# NET-68, adversarial round: is the domain jump an *additive base shift* or a
# *rescaling of the attention decay rate*?

`Applications.NET68DomainJumpBudgetLaw` fits the measured cells with the additive law
`k*(domain, ctx) = base(domain) + inc · doublings(ctx)`, `base(prose) = 16`,
`base(code) = 12`, `inc = 4`.  The Critic's objection: an additive fit of two points is
cheap.  A *mechanistic* alternative is that code attention decays geometrically at a
faster rate — `cum k = 1 - r^k` with `r_code = r_prose ^ a` for some `a > 1` — which
divides the knee rather than shifting it.

This file develops that alternative honestly and pushes both models to breaking point.

## Contents

*§1 Geometric profiles.*  `geomKnee r ρ` is the least budget with `r ^ k ≤ ρ`
(`ρ = 1 - τ` is the residual tolerance).  `geomKnee_eq_ceil` computes it exactly as
`⌈log ρ / log r⌉₊` — the **continuous knee** `X` of the domain — and
`geomKnee_rpow_eq_ceil_div` shows that raising the decay rate to the power `a` divides
the continuous knee by `a`.  `exists_geom_profile_with_continuous_knee`: every positive
`X` is realised by an actual geometric profile, so the model is not empty.

*§2 Ceiling calculus.*  `lt_of_ceil_eq`, `le_of_ceil_eq` — the exact bracket a knee
reading imposes on the continuous knee.

*§3 The two models on the measured data.*  `additive_model_matches` and
`rescaling_model_matches` (witness `a = 251/200`, `X_prose(512) = 15.05`,
`X_prose(1024) = 20`, geometrically realised by `rescaling_model_realisable`):
**both** reproduce all four measured knees.  `two_cells_do_not_identify_the_mechanism`
states the resulting identifiability failure — the honest limit of round 21.

*§4 The discriminating experiment.*  `rescaling_factor_gt_five_quarters`: the 512 cell
*forces* `a > 5/4` in any rescaling model.  `rescaling_prediction_4096_le_23`: every such
model then predicts at most `23` keys at 4096, whereas the additive law predicts exactly
`24` (`additive_prediction_4096_eq_24`).  `net69_discriminating_experiment`: the two
mechanisms are separated by a single measurement at ctx 4096 — and `separation_is_sharp`
shows one further doubling is genuinely needed, since at 2048 the models can still agree.
-/

open Catalog.NET68

open Real

/-! ## 1. Geometric attention profiles and the continuous knee -/

theorem Catalog.NET68.geomKnee_eq_ceil{r ρ : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hρ0 : 0 < ρ) :
    geomKnee r ρ = ⌈Real.log ρ / Real.log r⌉₊ := by sorry

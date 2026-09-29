-- Prove2me | Definitions.Def_Applications_NET68DecayRescalingAlternative
-- name    : Applications_NET68DecayRescalingAlternative
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:54:00.699555+00:00
-- url     : https://prove2.me/theorems/8b2fc325-ef4b-47d5-b655-f71b3fe90fe3
-- title:
--   Aether Catalog definitions — Applications_NET68DecayRescalingAlternative
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.NET68DecayRescalingAlternative`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/NET68DecayRescalingAlternative.lean by skeleton subtraction
import Mathlib
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

namespace Catalog.NET68

open Real

/-! ## 1. Geometric attention profiles and the continuous knee -/

/-- The knee of a geometrically decaying profile `cum k = 1 - r ^ k`: the least budget
whose residual mass `r ^ k` is within the residual tolerance `ρ = 1 - τ`. -/
noncomputable def geomKnee (r ρ : ℝ) : ℕ := sInf {k : ℕ | r ^ k ≤ ρ}




/-! ## 2. What a knee reading says about the continuous knee -/



/-! ## 3. Both mechanisms fit the two measured cells -/





/-! ## 4. The experiment that separates them -/







end Catalog.NET68



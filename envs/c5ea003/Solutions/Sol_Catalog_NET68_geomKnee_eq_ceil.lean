-- Prove2me | solution 1 for Catalog.NET68.geomKnee_eq_ceil
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:56:02.440748+00:00
-- url     : https://prove2.me/submissions/91a451d7-98d1-460b-8e4a-765afa34ad95

-- Sol generated from Applications/NET68DecayRescalingAlternative.lean
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





/-! ## 2. What a knee reading says about the continuous knee -/



/-! ## 3. Both mechanisms fit the two measured cells -/





/-! ## 4. The experiment that separates them -/








open Catalog.NET68 in
theorem solution{r ρ : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hρ0 : 0 < ρ) :
    geomKnee r ρ = ⌈Real.log ρ / Real.log r⌉₊ := by
  have hL : Real.log r < 0 := Real.log_neg hr0 hr1
  set X : ℝ := Real.log ρ / Real.log r with hX
  have hmem : ∀ k : ℕ, r ^ k ≤ ρ ↔ X ≤ (k : ℝ) := by
    intro k
    have hpow : (0 : ℝ) < r ^ k := pow_pos hr0 k
    rw [← Real.log_le_log_iff hpow hρ0, Real.log_pow, hX, div_le_iff_of_neg hL]
  have hceil : X ≤ (⌈X⌉₊ : ℝ) := Nat.le_ceil X
  have h1 : ⌈X⌉₊ ∈ {k : ℕ | r ^ k ≤ ρ} := (hmem _).2 hceil
  have h2 : ∀ k ∈ {k : ℕ | r ^ k ≤ ρ}, ⌈X⌉₊ ≤ k := fun k hk =>
    Nat.ceil_le.2 ((hmem k).1 hk)
  exact le_antisymm (Nat.sInf_le h1) (h2 _ (Nat.sInf_mem ⟨_, h1⟩))

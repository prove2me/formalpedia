-- Prove2me | solution 1 for Catalog.NET68.no_rescaling_model_fits_512_and_4096
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:00:17.626601+00:00
-- url     : https://prove2.me/submissions/d8b47591-c21c-41cd-9e0d-0bc7a196bf11

-- Sol generated from Applications/NET68DecayRescalingAlternative.lean
import Mathlib
import Definitions.Def_Applications_NET68DecayRescalingAlternative
import Definitions.Def_Applications_NET68DomainJumpBudgetLaw
import Theorems.Thm_Catalog_NET68_rescaling_factor_gt_five_quarters
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

/-- A knee reading `n ≥ 1` forces `X ≤ n`. -/
theorem le_of_ceil_eq {X : ℝ} {n : ℕ} (h : ⌈X⌉₊ = n) : X ≤ (n : ℝ) :=
  Nat.ceil_le.1 h.le

/-- A knee reading `n ≥ 1` forces `n - 1 < X`. -/
theorem lt_of_ceil_eq {X : ℝ} {n : ℕ} (hn : 0 < n) (h : ⌈X⌉₊ = n) : ((n : ℝ) - 1) < X := by
  have : n - 1 < ⌈X⌉₊ := by omega
  have h' : ((n - 1 : ℕ) : ℝ) < X := Nat.lt_ceil.1 this
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    have : (1 : ℕ) ≤ n := hn
    push_cast [Nat.cast_sub this]
    ring
  linarith [hcast ▸ h']

/-! ## 3. Both mechanisms fit the two measured cells -/





/-! ## 4. The experiment that separates them -/








open Catalog.NET68 in
theorem solution{a X0 X3 : ℝ} (ha : 0 < a)
    (h16 : ⌈X0⌉₊ = 16) (h12 : ⌈X0 / a⌉₊ = 12)
    (h28 : ⌈X3⌉₊ = 28) (h24 : ⌈X3 / a⌉₊ = 24) : False := by
  have hlow : 5 / 4 < a := rescaling_factor_gt_five_quarters ha h16 h12
  have hup : X3 ≤ 28 := by
    have := le_of_ceil_eq (n := 28) h28
    norm_num at this
    linarith
  have h23 : (23 : ℝ) < X3 / a := by
    have := lt_of_ceil_eq (n := 24) (by norm_num) h24
    norm_num at this
    linarith
  rw [lt_div_iff₀ ha] at h23
  linarith

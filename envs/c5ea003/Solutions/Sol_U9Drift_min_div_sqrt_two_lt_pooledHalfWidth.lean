-- Prove2me | solution 1 for U9Drift.min_div_sqrt_two_lt_pooledHalfWidth
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:50:39.468957+00:00
-- url     : https://prove2.me/submissions/5489026c-15d9-4cf3-998c-e99c9ccd03bb

-- Sol generated from Probability/U9DriftPooling.lean
import Mathlib
import Definitions.Def_Probability_U9DriftIntervals
import Definitions.Def_Probability_U9DriftPooling
import Theorems.Thm_U9Drift_lt_of_sq_lt_sq_nonneg
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.
-/

/-!
# Pooling the pilot and the fresh-seed replication: what "√2-tightened" really buys

Context (experiment 569, paper 216).  The round-74 ledger pools paper 214's pilot interval
for the band-9 smoothness ratio with the fresh-seed replication interval and reports a
"√2-tightened joint point ≈ 0.97".  This file develops the exact algebra of pooling two
independent estimates, and then audits that sentence against the ledger's own numbers.

The general theory:

* `U9Drift.poolVar_optimal` — for two independent estimates with variances `v₁, v₂ > 0`,
  every affine combination `w·x₁ + (1-w)·x₂` has variance at least
  `poolVar v₁ v₂ = v₁v₂/(v₁+v₂)`, with equality exactly at the inverse-variance weight
  `w = v₂/(v₁+v₂)` (`U9Drift.poolVar_attained`, `U9Drift.poolVar_optimal_strict`).
* `U9Drift.pooledHalfWidth_lt_left` / `_lt_right` — pooling is a strict gain over either
  input.
* `U9Drift.pooledHalfWidth_eq_of_eq` — at *matched* precisions the gain is exactly the
  advertised factor `√2`.
* `U9Drift.min_div_sqrt_two_le_pooledHalfWidth` — and `√2` is the *best possible* gain:
  for any precisions the pooled half width is at least `min/√2`, strictly so when the two
  precisions differ (`U9Drift.min_div_sqrt_two_lt_pooledHalfWidth`).

The audit of the ledger:

* `U9Drift.joint_interval_covers_one` — the inverse-variance pooled 95% interval of the two
  runs still covers `1` (`p ≈ 0.9617`, half width `≈ 0.04045`, upper edge `≈ 1.0021`).  So
  pooling does *not* resurrect the drift: the downgrade from "banked" to "open" is correct.
* `U9Drift.sqrt_two_tightening_fails` — the two runs are *not* precision-matched
  (`h_pilot ≈ 1.93 · h_rep`), so the realised tightening is far short of `√2`: the pooled
  half width strictly exceeds `h_rep/√2`.
* `U9Drift.equal_weight_pooling_overstates_the_drift` — the quoted joint point `≈ 0.97` is
  the *equal-weight* average of the two point estimates; the correct inverse-variance
  pooled point is strictly closer to `1`.  The ledger's own summary therefore overstates
  the residual tension.
-/

open U9Drift

open Real

/-! ## Inverse-variance pooling is optimal -/








/-! ## Pooling in the half-width parameterisation -/




theorem pooledHalfWidth_pos {h₁ h₂ : ℝ} (a₁ : 0 < h₁) (a₂ : 0 < h₂) :
    0 < pooledHalfWidth h₁ h₂ := by
  have : 0 < Real.sqrt (h₁ ^ 2 + h₂ ^ 2) := Real.sqrt_pos.mpr (by positivity)
  exact div_pos (mul_pos a₁ a₂) this

theorem pooledHalfWidth_sq {h₁ h₂ : ℝ} (a₁ : 0 < h₁) (a₂ : 0 < h₂) :
    pooledHalfWidth h₁ h₂ ^ 2 = h₁ ^ 2 * h₂ ^ 2 / (h₁ ^ 2 + h₂ ^ 2) := by
  have hs : (0:ℝ) < h₁ ^ 2 + h₂ ^ 2 := by positivity
  rw [pooledHalfWidth, div_pow, Real.sq_sqrt hs.le, mul_pow]






/-! ## Auditing the round-74 pooled claim -/









/-! ### Equal-weight versus inverse-variance pooling of the two point estimates -/






open U9Drift in
theorem solution{h₁ h₂ : ℝ} (a₁ : 0 < h₁) (a₂ : 0 < h₂)
    (hne : h₁ ≠ h₂) : min h₁ h₂ / Real.sqrt 2 < pooledHalfWidth h₁ h₂ := by
  have hs : (0:ℝ) < h₁ ^ 2 + h₂ ^ 2 := by positivity
  have hsq : (min h₁ h₂ / Real.sqrt 2) ^ 2 = min h₁ h₂ ^ 2 / 2 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  refine lt_of_sq_lt_sq_nonneg (by positivity) (pooledHalfWidth_pos a₁ a₂).le ?_
  rw [hsq, pooledHalfWidth_sq a₁ a₂, div_lt_div_iff₀ (by norm_num) hs]
  rcases min_cases h₁ h₂ with ⟨he, hle⟩ | ⟨he, hle⟩ <;> rw [he]
  · have hlt : h₁ < h₂ := lt_of_le_of_ne hle hne
    have hsq12 : h₁ ^ 2 < h₂ ^ 2 := by nlinarith
    nlinarith [mul_lt_mul_of_pos_left hsq12 (pow_pos a₁ 2)]
  · have hsq21 : h₂ ^ 2 < h₁ ^ 2 := by nlinarith
    nlinarith [mul_lt_mul_of_pos_left hsq21 (pow_pos a₂ 2)]

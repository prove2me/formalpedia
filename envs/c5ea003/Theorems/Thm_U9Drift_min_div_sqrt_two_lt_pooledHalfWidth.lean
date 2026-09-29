-- Prove2me | Theorems.Thm_U9Drift_min_div_sqrt_two_lt_pooledHalfWidth
-- name    : U9Drift.min_div_sqrt_two_lt_pooledHalfWidth
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:22:53.972269+00:00
-- url     : https://prove2.me/theorems/f1d796f2-606c-4644-9573-9d5ef1df0ff9
-- title:
--   ...and the `√2` gain is *strictly* out of reach whenever the precisions differ.
-- statement:
--   ...and the `√2` gain is *strictly* out of reach whenever the precisions differ.
--
--   ```lean
--   theorem U9Drift.min_div_sqrt_two_lt_pooledHalfWidth{h₁ h₂ : ℝ} (a₁ : 0 < h₁) (a₂ : 0 < h₂)
--       (hne : h₁ ≠ h₂) : min h₁ h₂ / Real.sqrt 2 < pooledHalfWidth h₁ h₂ := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/U9DriftPooling.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/U9DriftPooling.lean#L153

-- Thm stub generated from Probability/U9DriftPooling.lean
import Mathlib
import Definitions.Def_Probability_U9DriftIntervals
import Definitions.Def_Probability_U9DriftPooling
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

theorem U9Drift.min_div_sqrt_two_lt_pooledHalfWidth{h₁ h₂ : ℝ} (a₁ : 0 < h₁) (a₂ : 0 < h₂)
    (hne : h₁ ≠ h₂) : min h₁ h₂ / Real.sqrt 2 < pooledHalfWidth h₁ h₂ := by sorry

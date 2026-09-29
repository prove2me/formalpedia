-- Prove2me | Definitions.Def_Probability_U9DriftPooling
-- name    : Probability_U9DriftPooling
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:44:02.800734+00:00
-- url     : https://prove2.me/theorems/805b8beb-5a6c-4722-abf5-609c943d8a68
-- title:
--   Aether Catalog definitions — Probability_U9DriftPooling
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.U9DriftPooling`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/U9DriftPooling.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Probability_U9DriftIntervals
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

namespace U9Drift

open Real

/-! ## Inverse-variance pooling is optimal -/

/-- The variance of the inverse-variance pooled estimator. -/
noncomputable def poolVar (v₁ v₂ : ℝ) : ℝ := v₁ * v₂ / (v₁ + v₂)

/-- The inverse-variance weight put on the first estimate. -/
noncomputable def poolWeightVar (v₁ v₂ : ℝ) : ℝ := v₂ / (v₁ + v₂)






/-! ## Pooling in the half-width parameterisation -/

/-- The pooled half width of two intervals with half widths `h₁, h₂` (same coverage
factor): `h₁h₂/√(h₁²+h₂²)`. -/
noncomputable def pooledHalfWidth (h₁ h₂ : ℝ) : ℝ := h₁ * h₂ / Real.sqrt (h₁ ^ 2 + h₂ ^ 2)

/-- The inverse-variance weight on the first estimate, in terms of half widths. -/
noncomputable def poolWeight (h₁ h₂ : ℝ) : ℝ := h₂ ^ 2 / (h₁ ^ 2 + h₂ ^ 2)

/-- The pooled point estimate. -/
noncomputable def poolPoint (p₁ h₁ p₂ h₂ : ℝ) : ℝ :=
  poolWeight h₁ h₂ * p₁ + (1 - poolWeight h₁ h₂) * p₂








/-! ## Auditing the round-74 pooled claim -/









/-! ### Equal-weight versus inverse-variance pooling of the two point estimates -/

/-- Paper 214's reported point estimate at the `1e6` cut. -/
def pilotPoint : ℝ := 0.947

/-- Experiment 569's reported point estimate at the `1e6` cut. -/
def repPoint : ℝ := 0.99



end U9Drift



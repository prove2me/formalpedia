-- Prove2me | Theorems.Thm_U9Drift_ecov_eq_emean_mul_sub
-- name    : U9Drift.ecov_eq_emean_mul_sub
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:22:07.879664+00:00
-- url     : https://prove2.me/theorems/c0181c1b-5a80-4706-bd1f-e4f54e8b1e12
-- title:
--   The covariance in product form: `Cov(X, Y) = E[XY] - E[X]E[Y]`.
-- statement:
--   The covariance in product form: `Cov(X, Y) = E[XY] - E[X]E[Y]`.
--
--   ```lean
--   theorem U9Drift.ecov_eq_emean_mul_sub(f g : Fin n → ℝ) (hn : 0 < n) :
--       ecov f g = emean (fun i => f i * g i) - emean f * emean g := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/U9DriftPaired.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/U9DriftPaired.lean#L117

-- Thm stub generated from Probability/U9DriftPaired.lean
import Mathlib
import Definitions.Def_Probability_U9DriftPaired
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.
-/

/-!
# Why paired controls are the right design: empirical variance of a matched contrast

Context (experiment 569, paper 216).  The band-9 replication draws, for every candidate
value `j² - N`, a *paired* control of the same bit length and the same 3-bit mantissa head,
and runs both through the identical smoothness classifier.  The ledger asserts that control
integrity is then "satisfied by construction".  This file supplies the quantitative content
of that assertion: for the empirical contrast `X - Y` over the realised sample, pairing pays
exactly the covariance.

Main results (all for the empirical, finite-sample functionals over `Fin n`):

* `U9Drift.evar_sub` — the exact decomposition
  `Var(X - Y) = Var X + Var Y - 2 Cov(X, Y)`.
* `U9Drift.ecov_sq_le` — Cauchy–Schwarz for the empirical covariance,
  `Cov(X, Y)² ≤ Var X · Var Y`, hence the contrast variance is never worse than
  `(√Var X + √Var Y)²` and never better than `0`.
* `U9Drift.paired_beats_unpaired_iff` — pairing strictly beats independent sampling exactly
  when the induced covariance is positive.
* `U9Drift.ecov_eq_emean_mul_sub` — the covariance of two indicator sequences is
  `(agreement-on-1 rate) - p·q`: matching helps precisely to the extent that a candidate
  being smooth predicts its matched control being smooth.
* `U9Drift.evar_indicator` — for indicators `Var X = p(1-p)`, so the paired contrast of two
  rare events (`p, q ≈ 3·10⁻⁵`, as at band 9) has variance essentially `p + q - 2·(joint
  rate)`, which the pairing drives down.
* `U9Drift.evar_sub_self` — the degenerate extreme: a perfectly predictive pairing gives a
  zero-variance contrast.
-/

open U9Drift

open Finset

variable {n : ℕ}

/-! ## Empirical functionals -/







/-! ## The paired-contrast decomposition -/






/-! ## Indicator sequences: what the matching actually buys -/

theorem U9Drift.ecov_eq_emean_mul_sub(f g : Fin n → ℝ) (hn : 0 < n) :
    ecov f g = emean (fun i => f i * g i) - emean f * emean g := by sorry

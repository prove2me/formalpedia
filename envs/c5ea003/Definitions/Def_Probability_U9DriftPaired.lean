-- Prove2me | Definitions.Def_Probability_U9DriftPaired
-- name    : Probability_U9DriftPaired
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:39:59.44359+00:00
-- url     : https://prove2.me/theorems/f47c73b1-172b-4575-9007-396d829dfd73
-- title:
--   Aether Catalog definitions — Probability_U9DriftPaired
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.U9DriftPaired`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/U9DriftPaired.lean by skeleton subtraction
import Mathlib
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

namespace U9Drift

open Finset

variable {n : ℕ}

/-! ## Empirical functionals -/

/-- Empirical mean over the `n` sampled units. -/
noncomputable def emean (f : Fin n → ℝ) : ℝ := (∑ i, f i) / n

/-- Empirical variance over the `n` sampled units. -/
noncomputable def evar (f : Fin n → ℝ) : ℝ := (∑ i, (f i - emean f) ^ 2) / n

/-- Empirical covariance over the `n` sampled units. -/
noncomputable def ecov (f g : Fin n → ℝ) : ℝ :=
  (∑ i, (f i - emean f) * (g i - emean g)) / n




/-! ## The paired-contrast decomposition -/






/-! ## Indicator sequences: what the matching actually buys -/






end U9Drift



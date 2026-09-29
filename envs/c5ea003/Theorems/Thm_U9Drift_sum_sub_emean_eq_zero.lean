-- Prove2me | Theorems.Thm_U9Drift_sum_sub_emean_eq_zero
-- name    : U9Drift.sum_sub_emean_eq_zero
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:20:10.48171+00:00
-- url     : https://prove2.me/theorems/f2c76096-2019-4510-bbee-8d743375e30f
-- title:
--   Sum sub emean eq zero
-- statement:
--   Formal statement of `U9Drift.sum_sub_emean_eq_zero` from the Aether Catalog (Probability). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem U9Drift.sum_sub_emean_eq_zero{n : ℕ} (hn : 0 < n) (f : Fin n → ℝ) :
--       ∑ j, (f j - emean f) = 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/U9DriftClusterVariance.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/U9DriftClusterVariance.lean#L37

-- Thm stub generated from Probability/U9DriftClusterVariance.lean
import Mathlib
import Definitions.Def_Probability_U9DriftClusterVariance
import Definitions.Def_Probability_U9DriftPaired
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.
-/

/-!
# Cluster decomposition of the dispersion: why `128` clusters, not `19.2·10⁶` pairs

Context (experiment 569, paper 216).  The run draws `m = 128` moduli `N` and `n = 150000`
candidate/control pairs inside each, and bootstraps over the `N`-clusters.  The previous
file (`Probability.U9DriftLocalDensity`) shows *why* the between-cluster dispersion is
large; this file proves the exact identity that converts that fact into a design rule.

Main results:

* `U9Drift.sum_sub_emean_eq_zero` — the residuals inside a cluster sum to zero.
* `U9Drift.sum_sq_sub_const` — the bias–variance shift: `∑ (x - c)² = ∑ (x - x̄)² + n(x̄ - c)²`,
  and hence `U9Drift.evar_le_mean_sq_sub` — the empirical variance is the *minimum* over
  centres.
* `U9Drift.anova_decomposition` — for a balanced two-level design the total dispersion
  splits exactly as `total = within + between`.
* `U9Drift.between_le_total` — the between-cluster variance is a lower bound for the total
  dispersion: no amount of within-cluster sampling can shrink it.
* `U9Drift.pairs_cannot_beat_clusters` — the quantitative design rule: whatever the number
  of pairs per cluster, the dispersion of the design is at least the between-cluster
  variance, which by `U9Drift.variance_signProd` is exponentially large in the number of
  small primes.  Only increasing the cluster count `m` helps.
-/

open U9Drift

open Finset

/-! ## Residuals and the shift identity -/

theorem U9Drift.sum_sub_emean_eq_zero{n : ℕ} (hn : 0 < n) (f : Fin n → ℝ) :
    ∑ j, (f j - emean f) = 0 := by sorry

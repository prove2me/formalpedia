-- Prove2me | solution 1 for U9Drift.between_le_total
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:38:38.659622+00:00
-- url     : https://prove2.me/submissions/37ed1d4c-c408-42d2-bce4-935b15cd1d90

-- Sol generated from Probability/U9DriftClusterVariance.lean
import Mathlib
import Definitions.Def_Probability_U9DriftClusterVariance
import Definitions.Def_Probability_U9DriftPaired
import Theorems.Thm_U9Drift_anova_decomposition
import Theorems.Thm_U9Drift_evar_nonneg
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




/-! ## The balanced two-level (ANOVA) decomposition -/










open U9Drift in
theorem solution{m n : ℕ} (hm : 0 < m) (hn : 0 < n) (x : Fin m → Fin n → ℝ) :
    betweenVar x ≤ totalVar x := by
  rw [anova_decomposition hm hn x]
  have hw : 0 ≤ withinVar x := by
    rw [withinVar, emean]
    apply div_nonneg _ (Nat.cast_nonneg m)
    exact Finset.sum_nonneg fun i _ => evar_nonneg (x i)
  linarith

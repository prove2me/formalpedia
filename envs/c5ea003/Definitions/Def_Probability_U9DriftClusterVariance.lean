-- Prove2me | Definitions.Def_Probability_U9DriftClusterVariance
-- name    : Probability_U9DriftClusterVariance
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:40:49.057733+00:00
-- url     : https://prove2.me/theorems/6c7f33e5-0ed1-4387-87e3-7d10860142a0
-- title:
--   Aether Catalog definitions — Probability_U9DriftClusterVariance
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.U9DriftClusterVariance`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/U9DriftClusterVariance.lean by skeleton subtraction
import Mathlib
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

namespace U9Drift

open Finset

/-! ## Residuals and the shift identity -/




/-! ## The balanced two-level (ANOVA) decomposition -/

/-- Mean of cluster `i`. -/
noncomputable def clusterMean {m n : ℕ} (x : Fin m → Fin n → ℝ) (i : Fin m) : ℝ :=
  emean (x i)

/-- Grand mean of a balanced design. -/
noncomputable def grandMean {m n : ℕ} (x : Fin m → Fin n → ℝ) : ℝ :=
  emean (clusterMean x)

/-- Mean within-cluster variance. -/
noncomputable def withinVar {m n : ℕ} (x : Fin m → Fin n → ℝ) : ℝ :=
  emean (fun i => evar (x i))

/-- Between-cluster variance of the cluster means. -/
noncomputable def betweenVar {m n : ℕ} (x : Fin m → Fin n → ℝ) : ℝ :=
  evar (clusterMean x)

/-- Total dispersion of all `m·n` observations about the grand mean. -/
noncomputable def totalVar {m n : ℕ} (x : Fin m → Fin n → ℝ) : ℝ :=
  (∑ i, ∑ j, (x i j - grandMean x) ^ 2) / ((m : ℝ) * n)




end U9Drift



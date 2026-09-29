-- Prove2me | Theorems.Thm_U9Drift_sum_resample_eval_pair
-- name    : U9Drift.sum_resample_eval_pair
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:20:35.08768+00:00
-- url     : https://prove2.me/theorems/cf6ff13c-79f5-4274-a496-26ac263ca909
-- title:
--   Marginalising all coordinates but two distinct ones.
-- statement:
--   Marginalising all coordinates but two distinct ones.
--
--   ```lean
--   theorem U9Drift.sum_resample_eval_pair(g h : Fin m → ℝ) {k l : Fin m} (hkl : k ≠ l) :
--       ∑ s : Fin m → Fin m, g (s k) * h (s l)
--         = (m : ℝ) ^ (m - 2) * ((∑ i, g i) * (∑ i, h i)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/U9DriftBootstrapVariance.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/U9DriftBootstrapVariance.lean#L88

-- Thm stub generated from Probability/U9DriftBootstrapVariance.lean
import Mathlib
import Definitions.Def_Probability_U9DriftBootstrapVariance
import Definitions.Def_Probability_U9DriftClusterVariance
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.
-/

/-!
# The cluster bootstrap has variance exactly `between / m`

Context (experiment 569, paper 216).  The run reports percentile intervals from a
*cluster bootstrap*: the `m = 128` moduli are resampled with replacement (`NB = 2000`
draws) and the ratio statistic is recomputed from the resampled clusters.  Conjecture
**C3** of `FUTURE_DIRECTIONS.md` asserts that the pair count `n` per modulus is not a
power lever: the spread of the bootstrap distribution is governed by the *cluster* count.

This file closes the structural half of that conjecture, exactly and without asymptotics.
The bootstrap resample space is the finite set of all `m ^ m` index maps
`s : Fin m → Fin m`, each equally likely, and the resampled statistic is the mean of the
resampled cluster values.

Main results.

* `U9Drift.sum_resample_prod` — the marginalisation identity for the resample space:
  `∑_{s} ∏_i F i (s i) = ∏_i ∑_j F i j`.  This is the exact finite-sample form of
  "the resample coordinates are independent".
* `U9Drift.sum_resample_eval` and `U9Drift.sum_resample_eval_pair` — its one- and
  two-coordinate corollaries, `m ^ (m-1) ∑ g` and `m ^ (m-2) (∑ g)(∑ h)`.
* `U9Drift.bootVar_eq` — **the exact bootstrap variance law**: for any cluster values `c`,
  the variance of the resample mean over the whole resample space is `evar c / m`.
  No asymptotics, no approximation: the `1 / m` is exact at every `m`.
* `U9Drift.cluster_bootVar_eq` — applied to a balanced two-level design, the cluster
  bootstrap variance is exactly `betweenVar x / m` and therefore does not involve the
  within-cluster dispersion at all: the pair count `n` enters only through the value of
  `betweenVar`.
* `U9Drift.bootVar_le_totalVar_div` and `U9Drift.clusters_needed_iff` — the design rule in
  the form the follow-up run needs: to reach a target bootstrap standard error `t` one
  needs `m ≥ evar c / t²` clusters, whatever the pair count.
* `U9Drift.bootVar_pos_of_ne` — non-degeneracy: the bootstrap spread vanishes only for a
  constant cluster population, so the interval is never artificially tight.
-/

open U9Drift

open Finset

variable {m : ℕ}

/-! ## Marginalisation over the resample space -/

theorem U9Drift.sum_resample_eval_pair(g h : Fin m → ℝ) {k l : Fin m} (hkl : k ≠ l) :
    ∑ s : Fin m → Fin m, g (s k) * h (s l)
      = (m : ℝ) ^ (m - 2) * ((∑ i, g i) * (∑ i, h i)) := by sorry

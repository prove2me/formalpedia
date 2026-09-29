-- Prove2me | Definitions.Def_Probability_U9DriftBootstrapVariance
-- name    : Probability_U9DriftBootstrapVariance
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:42:29.556447+00:00
-- url     : https://prove2.me/theorems/3c4db296-52b9-4c2d-a066-e807762b903f
-- title:
--   Aether Catalog definitions — Probability_U9DriftBootstrapVariance
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.U9DriftBootstrapVariance`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/U9DriftBootstrapVariance.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Probability_U9DriftClusterVariance
import Definitions.Def_Probability_U9DriftPaired
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

namespace U9Drift

open Finset

variable {m : ℕ}

/-! ## Marginalisation over the resample space -/




/-! ## The bootstrap variance law -/

/-- The mean of the resample indexed by `s`. -/
noncomputable def bootMean (c : Fin m → ℝ) (s : Fin m → Fin m) : ℝ :=
  emean fun k => c (s k)

/-- The variance of the resample mean over the whole resample space of `m ^ m` maps,
centred at the population mean (which is the bootstrap expectation of the resample mean). -/
noncomputable def bootVar (c : Fin m → ℝ) : ℝ :=
  (∑ s : Fin m → Fin m, (bootMean c s - emean c) ^ 2) / (m : ℝ) ^ m



/-! ## Consequences for the design -/






end U9Drift



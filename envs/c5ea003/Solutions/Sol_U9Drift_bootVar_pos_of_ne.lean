-- Prove2me | solution 1 for U9Drift.bootVar_pos_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:42:54.075237+00:00
-- url     : https://prove2.me/submissions/6e4fbfc9-68bc-42bc-b5b5-085443426942

-- Sol generated from Probability/U9DriftBootstrapVariance.lean
import Mathlib
import Definitions.Def_Probability_U9DriftBootstrapVariance
import Definitions.Def_Probability_U9DriftClusterVariance
import Definitions.Def_Probability_U9DriftPaired
import Theorems.Thm_U9Drift_bootVar_eq
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




/-! ## The bootstrap variance law -/





/-! ## Consequences for the design -/







open U9Drift in
theorem solution(hm : 0 < m) {c : Fin m → ℝ} {a b : Fin m} (hab : c a ≠ c b) :
    0 < bootVar c := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  rw [bootVar_eq hm c, evar]
  refine div_pos (div_pos ?_ hmR) hmR
  have hnonneg : ∀ i ∈ (univ : Finset (Fin m)), 0 ≤ (c i - emean c) ^ 2 :=
    fun i _ => sq_nonneg _
  rcases lt_or_eq_of_le (Finset.sum_nonneg hnonneg) with h | h
  · exact h
  · exfalso
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp h.symm
    have ha : c a - emean c = 0 := by
      have := hzero a (Finset.mem_univ a)
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    have hb : c b - emean c = 0 := by
      have := hzero b (Finset.mem_univ b)
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    exact hab (by linarith)

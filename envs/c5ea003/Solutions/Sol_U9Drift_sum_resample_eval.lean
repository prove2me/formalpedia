-- Prove2me | solution 1 for U9Drift.sum_resample_eval
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:38:39.703445+00:00
-- url     : https://prove2.me/submissions/0ac67625-513a-47bb-8a68-f9aaff2240e9

-- Sol generated from Probability/U9DriftBootstrapVariance.lean
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

/-- **Exact independence of the resample coordinates.**  Summing a product of
coordinatewise weights over all `m ^ m` resample maps factors as a product of sums. -/
theorem sum_resample_prod (F : Fin m → Fin m → ℝ) :
    ∑ s : Fin m → Fin m, ∏ i, F i (s i) = ∏ i, ∑ j, F i j := by
  classical
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]



/-! ## The bootstrap variance law -/





/-! ## Consequences for the design -/







open U9Drift in
theorem solution(g : Fin m → ℝ) (k : Fin m) :
    ∑ s : Fin m → Fin m, g (s k) = (m : ℝ) ^ (m - 1) * ∑ i, g i := by
  classical
  have h := sum_resample_prod (m := m) (fun i j => if i = k then g j else 1)
  have hl : ∀ s : Fin m → Fin m,
      (∏ i, if i = k then g (s i) else (1 : ℝ)) = g (s k) := by
    intro s
    simp
  have hr : ∀ i : Fin m, (∑ j, if i = k then g j else (1 : ℝ))
      = if i = k then (∑ j, g j) else (m : ℝ) := by
    intro i
    by_cases hik : i = k
    · simp [hik]
    · simp [hik]
  have hprod : (∏ i : Fin m, if i = k then (∑ j, g j) else (m : ℝ))
      = (∑ j, g j) * (m : ℝ) ^ (m - 1) := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k), if_pos rfl]
    congr 1
    rw [Finset.prod_congr rfl (fun i hi => if_neg (Finset.ne_of_mem_erase hi)),
      Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ,
      Fintype.card_fin]
  calc ∑ s : Fin m → Fin m, g (s k)
      = ∑ s : Fin m → Fin m, ∏ i, (if i = k then g (s i) else (1 : ℝ)) := by
        exact (Finset.sum_congr rfl fun s _ => (hl s).symm)
    _ = ∏ i : Fin m, ∑ j, (if i = k then g j else (1 : ℝ)) := h
    _ = ∏ i : Fin m, (if i = k then (∑ j, g j) else (m : ℝ)) :=
        Finset.prod_congr rfl fun i _ => hr i
    _ = (∑ j, g j) * (m : ℝ) ^ (m - 1) := hprod
    _ = (m : ℝ) ^ (m - 1) * ∑ i, g i := by ring

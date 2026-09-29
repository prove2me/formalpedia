-- Prove2me | solution 1 for U9Drift.bootVar_eq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:40:31.771594+00:00
-- url     : https://prove2.me/submissions/4dfb4f50-84e4-4e1b-af72-668fe7593ea6

-- Sol generated from Probability/U9DriftBootstrapVariance.lean
import Mathlib
import Definitions.Def_Probability_U9DriftBootstrapVariance
import Definitions.Def_Probability_U9DriftClusterVariance
import Definitions.Def_Probability_U9DriftPaired
import Theorems.Thm_U9Drift_sum_resample_eval
import Theorems.Thm_U9Drift_sum_resample_eval_pair
import Theorems.Thm_U9Drift_sum_sub_emean_eq_zero
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



/-- Recentring a resample mean. -/
theorem bootMean_sub (hm : 0 < m) (c : Fin m → ℝ) (s : Fin m → Fin m) :
    bootMean c s - emean c = (∑ k, (c (s k) - emean c)) / m := by
  have hmR : ((m : ℝ)) ≠ 0 := by
    have : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    exact ne_of_gt this
  rw [bootMean, emean, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp


/-! ## Consequences for the design -/







open U9Drift in
theorem solution(hm : 0 < m) (c : Fin m → ℝ) : bootVar c = evar c / m := by
  classical
  set d : Fin m → ℝ := fun i => c i - emean c with hd
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hd0 : ∑ i, d i = 0 := sum_sub_emean_eq_zero hm c
  -- expand the square of the resample sum
  have hsq : ∀ s : Fin m → Fin m,
      (∑ k, d (s k)) ^ 2 = ∑ k, ∑ l, d (s k) * d (s l) := by
    intro s
    rw [sq, Finset.sum_mul_sum]
  have hoff : ∀ k l : Fin m, k ≠ l → ∑ s : Fin m → Fin m, d (s k) * d (s l) = 0 := by
    intro k l hkl
    rw [sum_resample_eval_pair d d hkl, hd0]
    ring
  have hdiag : ∀ k : Fin m, ∑ s : Fin m → Fin m, d (s k) * d (s k)
      = (m : ℝ) ^ (m - 1) * ∑ i, d i ^ 2 := by
    intro k
    have := sum_resample_eval (fun i => d i * d i) k
    simpa [sq] using this
  have hmm : (m : ℝ) ^ (m - 1) * (m : ℝ) = (m : ℝ) ^ m := by
    rw [← pow_succ]
    congr 1
    omega
  have hkey : ∑ s : Fin m → Fin m, (∑ k, d (s k)) ^ 2
      = (m : ℝ) ^ m * ∑ i, d i ^ 2 := by
    calc ∑ s : Fin m → Fin m, (∑ k, d (s k)) ^ 2
        = ∑ s : Fin m → Fin m, ∑ k, ∑ l, d (s k) * d (s l) :=
          Finset.sum_congr rfl fun s _ => hsq s
      _ = ∑ k, ∑ l, ∑ s : Fin m → Fin m, d (s k) * d (s l) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun k _ => Finset.sum_comm
      _ = ∑ k : Fin m, ∑ s : Fin m → Fin m, d (s k) * d (s k) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          refine Finset.sum_eq_single k (fun l _ hlk => hoff k l (Ne.symm hlk)) ?_
          intro hk
          exact absurd (Finset.mem_univ k) hk
      _ = ∑ _k : Fin m, (m : ℝ) ^ (m - 1) * ∑ i, d i ^ 2 :=
          Finset.sum_congr rfl fun k _ => hdiag k
      _ = (m : ℝ) ^ m * ∑ i, d i ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ← mul_assoc, mul_comm ((m : ℝ)) ((m : ℝ) ^ (m - 1)), hmm]
  have hmpow : ((m : ℝ) ^ m) ≠ 0 := pow_ne_zero _ (ne_of_gt hmR)
  have hterm : ∀ s : Fin m → Fin m,
      (bootMean c s - emean c) ^ 2 = (∑ k, d (s k)) ^ 2 / (m : ℝ) ^ 2 := by
    intro s
    rw [bootMean_sub hm c s, div_pow]
  rw [bootVar, Finset.sum_congr rfl fun s _ => hterm s, ← Finset.sum_div, hkey, evar]
  field_simp
  ring

-- Prove2me | solution 1 for UniversalRedundancy.tvDist_channel_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T03:40:57.316125+00:00
-- url     : https://prove2.me/submissions/4dfb28ca-09e5-4062-9927-65a0b7026737

-- Sol generated from MachineLearning/TotalVariation/Testing.lean
import Mathlib
import Definitions.Def_MachineLearning_TotalVariation_EventSup
import Definitions.Def_MachineLearning_TotalVariation_Testing
import Definitions.Def_MachineLearning_UniversalRedundancy_Rigidity
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Operational consequences of the sharp total-variation normalization

`MachineLearning.TotalVariation.EventSup` proved the factor-`1/2` characterization

`d_TV(p, q) = max_{A} (p(A) − q(A))`.

Here we cash it in.  Three classical pillars of statistical learning theory are
derived, each of them *tight* precisely because the normalization is the sharp
one:

1. **Le Cam's two-point bound.**  For the uniform-prior binary testing problem
   `p` vs `q`, the Bayes error of the best test is exactly `(1 − d_TV)/2`
   (`isLeast_bayesError`).  With the crude `ℓ¹` normalization one would only get
   the vacuous `(1 − ‖p − q‖₁)/2`, which is negative as soon as `‖p − q‖₁ > 1`.
2. **Data processing.**  Post-processing by an arbitrary stochastic channel — in
   particular by any deterministic feature map / statistic — cannot increase
   total variation (`tvDist_channel_le`, `tvDist_map_le`).
3. **Tensorization and sample complexity.**  `d_TV(p^{⊗n}, q^{⊗n}) ≤ n·d_TV(p, q)`
   (`tvDist_powLaw_le`), so a learner needs `n ≳ 1/d_TV` i.i.d. samples before it
   can tell the two sources apart at all (`bayesError_powLaw_ge`).

## Main results

* `bayesError_eq_half_one_add_eventGap`, `isLeast_bayesError`,
  `bayesError_ge_half_one_sub_tvDist` — Le Cam;
* `tvDist_channel_le`, `tvDist_map_le` — the data-processing inequality;
* `tvDist_prodLaw_le` — two-factor tensorization (hybrid argument);
* `tvDist_powLaw_le` — the `n`-sample bound by induction;
* `bayesError_powLaw_ge` — the resulting sample-complexity lower bound.

## Application keywords

Le Cam method, hypothesis testing, data processing inequality, tensorization,
sample complexity, indistinguishability, hybrid argument
-/


open Finset

open UniversalRedundancy

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-! ## Le Cam's two-point bound -/





/-! ## The data-processing inequality -/





/-! ## Tensorization -/




/-! ## `n` i.i.d. samples -/









open UniversalRedundancy in
theorem solution(p q : X → ℝ) {K : X → Y → ℝ} (hK0 : ∀ x y, 0 ≤ K x y)
    (hK : ∀ x, ∑ y, K x y = 1) :
    tvDist (channelPush p K) (channelPush q K) ≤ tvDist p q := by
  have key : ∑ y, |channelPush p K y - channelPush q K y| ≤ ∑ x, |p x - q x| := by
    calc ∑ y, |channelPush p K y - channelPush q K y|
        = ∑ y, |∑ x, (p x - q x) * K x y| := by
          refine Finset.sum_congr rfl fun y _ => ?_
          congr 1
          rw [channelPush, channelPush, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun x _ => by ring
      _ ≤ ∑ y, ∑ x, |p x - q x| * K x y := by
          refine Finset.sum_le_sum fun y _ => ?_
          refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun x _ => ?_)
          rw [abs_mul, abs_of_nonneg (hK0 x y)]
      _ = ∑ x, |p x - q x| := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [← Finset.mul_sum, hK x, mul_one]
  unfold tvDist
  linarith

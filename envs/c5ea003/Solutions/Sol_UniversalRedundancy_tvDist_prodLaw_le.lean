-- Prove2me | solution 1 for UniversalRedundancy.tvDist_prodLaw_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T03:45:51.448233+00:00
-- url     : https://prove2.me/submissions/4b10857a-bbab-46e4-a8f7-50b64ada7cb8

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
theorem solution{p₁ q₁ : X → ℝ} {p₂ q₂ : Y → ℝ}
    (hq₁0 : ∀ x, 0 ≤ q₁ x) (hq₁ : ∑ x, q₁ x = 1)
    (hp₂0 : ∀ y, 0 ≤ p₂ y) (hp₂ : ∑ y, p₂ y = 1) :
    tvDist (prodLaw p₁ p₂) (prodLaw q₁ q₂) ≤ tvDist p₁ q₁ + tvDist p₂ q₂ := by
  have key : ∑ z, |prodLaw p₁ p₂ z - prodLaw q₁ q₂ z|
      ≤ (∑ x, |p₁ x - q₁ x|) + ∑ y, |p₂ y - q₂ y| := by
    calc ∑ z, |prodLaw p₁ p₂ z - prodLaw q₁ q₂ z|
        = ∑ x, ∑ y, |p₁ x * p₂ y - q₁ x * q₂ y| := by
          rw [Fintype.sum_prod_type]; rfl
      _ ≤ ∑ x, ∑ y, (|p₁ x - q₁ x| * p₂ y + q₁ x * |p₂ y - q₂ y|) := by
          refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
          have hsplit : p₁ x * p₂ y - q₁ x * q₂ y
              = (p₁ x - q₁ x) * p₂ y + q₁ x * (p₂ y - q₂ y) := by ring
          rw [hsplit]
          refine le_trans (abs_add_le _ _) ?_
          rw [abs_mul, abs_mul, abs_of_nonneg (hp₂0 y), abs_of_nonneg (hq₁0 x)]
      _ = (∑ x, |p₁ x - q₁ x|) + ∑ y, |p₂ y - q₂ y| := by
          have h1 : ∀ x : X, ∑ y, (|p₁ x - q₁ x| * p₂ y + q₁ x * |p₂ y - q₂ y|)
              = |p₁ x - q₁ x| + q₁ x * ∑ y, |p₂ y - q₂ y| := by
            intro x
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hp₂, mul_one]
          rw [Finset.sum_congr rfl fun x _ => h1 x, Finset.sum_add_distrib,
            ← Finset.sum_mul, hq₁, one_mul]
  unfold tvDist
  linarith

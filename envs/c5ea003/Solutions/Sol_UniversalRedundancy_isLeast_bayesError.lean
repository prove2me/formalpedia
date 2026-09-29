-- Prove2me | solution 1 for UniversalRedundancy.isLeast_bayesError
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T02:29:45.480619+00:00
-- url     : https://prove2.me/submissions/917a30cc-8ca4-46d0-9160-ee514888ab6e

-- Sol generated from MachineLearning/TotalVariation/Testing.lean
import Mathlib
import Definitions.Def_MachineLearning_TotalVariation_EventSup
import Definitions.Def_MachineLearning_TotalVariation_Testing
import Definitions.Def_MachineLearning_UniversalRedundancy_Rigidity
import Theorems.Thm_UniversalRedundancy_abs_eventGap_le_tvDist
import Theorems.Thm_UniversalRedundancy_bayesError_eq_half_one_add_eventGap
import Theorems.Thm_UniversalRedundancy_eventGap_neg
import Theorems.Thm_UniversalRedundancy_eventGap_sepEvent
import Theorems.Thm_UniversalRedundancy_tvDist_comm
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
theorem solution{p q : X → ℝ} (hp : ∑ x, p x = 1) (hq : ∑ x, q x = 1) :
    IsLeast (Set.range (bayesError p q)) ((1 - tvDist p q) / 2) := by
  classical
  constructor
  · refine ⟨fun x => decide (p x ≤ q x), ?_⟩
    rw [bayesError_eq_half_one_add_eventGap hq]
    have hA : (univ.filter fun x => (decide (p x ≤ q x)) = true) = sepEvent q p := by
      rw [sepEvent]
      apply Finset.filter_congr
      intro x _
      simp
    rw [hA, ← eventGap_neg, eventGap_sepEvent hq hp, tvDist_comm q p]
    ring
  · rintro r ⟨f, rfl⟩
    rw [bayesError_eq_half_one_add_eventGap hq]
    have hbd := abs_eventGap_le_tvDist hp hq (univ.filter fun x => f x = true)
    have := neg_le_of_abs_le hbd
    linarith

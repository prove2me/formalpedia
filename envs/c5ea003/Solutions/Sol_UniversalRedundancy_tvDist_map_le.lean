-- Prove2me | solution 1 for UniversalRedundancy.tvDist_map_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T03:45:50.67655+00:00
-- url     : https://prove2.me/submissions/b18d18b5-d019-4317-a3e0-83971710e1d2

-- Sol generated from MachineLearning/TotalVariation/Testing.lean
import Mathlib
import Definitions.Def_MachineLearning_TotalVariation_EventSup
import Definitions.Def_MachineLearning_TotalVariation_Testing
import Definitions.Def_MachineLearning_UniversalRedundancy_Rigidity
import Theorems.Thm_UniversalRedundancy_tvDist_channel_le
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
theorem solution[DecidableEq Y] (p q : X → ℝ) (T : X → Y) :
    tvDist (fun y => ∑ x ∈ univ.filter fun x => T x = y, p x)
      (fun y => ∑ x ∈ univ.filter fun x => T x = y, q x) ≤ tvDist p q := by
  classical
  set K : X → Y → ℝ := fun x y => if T x = y then 1 else 0 with hKdef
  have hK0 : ∀ x y, 0 ≤ K x y := by
    intro x y; by_cases h : T x = y <;> simp [hKdef, h]
  have hK : ∀ x, ∑ y, K x y = 1 := by
    intro x
    simp [hKdef]
  have hpush : ∀ r : X → ℝ, channelPush r K
      = fun y => ∑ x ∈ univ.filter fun x => T x = y, r x := by
    intro r
    funext y
    rw [channelPush, Finset.sum_filter]
    exact Finset.sum_congr rfl fun x _ => by by_cases h : T x = y <;> simp [hKdef, h]
  have := tvDist_channel_le p q hK0 hK
  rwa [hpush p, hpush q] at this

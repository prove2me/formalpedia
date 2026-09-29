-- Prove2me | solution 1 for UniversalRedundancy.KLb_nml_le_logb_shtarkovSum
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T02:03:18.962749+00:00
-- url     : https://prove2.me/submissions/792e493d-d896-44c3-be5e-e7d4bdbd4381

-- Sol generated from MachineLearning/UniversalRedundancy/Capacity.lean
import Mathlib
import Definitions.Def_MachineLearning_UniversalRedundancy_Capacity
import Definitions.Def_MachineLearning_UniversalRedundancy_Core
import Theorems.Thm_UniversalRedundancy_SourceClass_prob_le_shtarkovSum_mul_nml
import Theorems.Thm_UniversalRedundancy_SourceClass_shtarkovSum_pos
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The Price of Universality IV: the redundancy–capacity lower bound

Fourth instalment of the thread.  `UniversalRedundancy.Core` computed the
*worst-case* (pointwise) minimax redundancy exactly: `log₂ Cₛ`.  This file
develops the *average-case* side, which produces lower bounds that do not
depend on any single bad message: the Bayes / capacity bound.

## Central Idea

Put a prior `w` on the class.  For any coding distribution `q`,

`∑_θ w_θ · D(p_θ ‖ q) = I(w) + D(m_w ‖ q)`   (compensation identity),

where `m_w = ∑_θ w_θ p_θ` is the mixture and `I(w) = ∑_θ w_θ D(p_θ ‖ m_w)` is
the mutual information between parameter and data.  Since relative entropy is
non-negative (Gibbs), the mixture code is Bayes optimal and

`I(w) ≤ inf_q sup_θ D(p_θ ‖ q) ≤ log₂ Cₛ`.

So the *capacity* of the class is a lower bound on the average redundancy of any
universal scheme, and it never exceeds the worst-case answer of Part I.  All
statements are for strictly positive laws and priors, the regime where relative
entropy is finite and the classical theory lives.

## Main Results

* `KLb`, `mixture`, `mutualInfo`, `bayesRedundancy` — relative entropy in bits,
  the Bayes mixture, the capacity functional, and Bayes-average redundancy
* `KLb_nonneg` — Gibbs' inequality
* `compensation_identity` — the exact Bayes decomposition
* `mutualInfo_le_bayesRedundancy` — the mixture code is Bayes optimal: no code
  beats `I(w)` on average
* `exists_source_KLb_ge_mutualInfo` — minimax ≥ maximin: every coding
  distribution suffers at least `I(w)` against some source of the class
* `mutualInfo_le_logb_shtarkovSum` — capacity never exceeds the worst-case price
  `log₂ Cₛ` of Part I, tying the two theories together
* `mutualInfo_le_entropy`, `entropyb_le_logb_card` — `I(w) ≤ H(w) ≤ log₂ #Θ`:
  the price of universality is at most the cost of *naming the source*

## Application Keywords

redundancy-capacity theorem, relative entropy, Gibbs inequality, Bayes mixture
code, mutual information, universal coding
-/


open Finset Real

open UniversalRedundancy

variable {X : Type*} [Fintype X] {Θ : Type*} [Fintype Θ] [Nonempty Θ]







variable (S : SourceClass X Θ)






/-! ## Capacity never exceeds the worst-case price -/



/-! ## Capacity is at most the entropy of the prior -/




open UniversalRedundancy in
omit [Fintype Θ] in
theorem solution(θ : Θ) (hp : ∀ θ x, 0 < S.prob θ x)
    (hmax : ∀ x, 0 < S.maxLik x) :
    KLb (S.prob θ) S.nml ≤ logb 2 S.shtarkovSum := by
  have hCpos := S.shtarkovSum_pos
  have hnml : ∀ x, 0 < S.nml x := fun x => div_pos (hmax x) hCpos
  have hterm : ∀ x, S.prob θ x * logb 2 (S.prob θ x / S.nml x)
      ≤ S.prob θ x * logb 2 S.shtarkovSum := by
    intro x
    refine mul_le_mul_of_nonneg_left ?_ (S.nonneg θ x)
    refine Real.logb_le_logb_of_le (by norm_num) (div_pos (hp θ x) (hnml x)) ?_
    rw [div_le_iff₀ (hnml x)]
    exact S.prob_le_shtarkovSum_mul_nml θ x
  calc KLb (S.prob θ) S.nml ≤ ∑ x, S.prob θ x * logb 2 S.shtarkovSum :=
        Finset.sum_le_sum fun x _ => hterm x
    _ = logb 2 S.shtarkovSum := by rw [← Finset.sum_mul, S.sum_one θ, one_mul]

-- Prove2me | solution 1 for UniversalRedundancy.mutualInfo_le_entropy
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T03:27:59.749849+00:00
-- url     : https://prove2.me/submissions/06c12b40-fd7d-48fc-bb64-77620734a2e1

-- Sol generated from MachineLearning/UniversalRedundancy/Capacity.lean
import Mathlib
import Definitions.Def_MachineLearning_UniversalRedundancy_Capacity
import Definitions.Def_MachineLearning_UniversalRedundancy_Core
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

lemma mixture_pos (w : Θ → ℝ) (hw : ∀ θ, 0 < w θ) (hp : ∀ θ x, 0 < S.prob θ x) (x : X) :
    0 < mixture S w x := by
  unfold mixture
  refine Finset.sum_pos (fun θ _ => mul_pos (hw θ) (hp θ x)) ⟨Classical.arbitrary Θ, mem_univ _⟩





/-! ## Capacity never exceeds the worst-case price -/



/-! ## Capacity is at most the entropy of the prior -/




open UniversalRedundancy in
theorem solution(w : Θ → ℝ) (hw : ∀ θ, 0 < w θ)
    (hp : ∀ θ x, 0 < S.prob θ x) : mutualInfo S w ≤ entropyb w := by
  have hm : ∀ x, 0 < mixture S w x := mixture_pos S w hw hp
  have hKL : ∀ θ, KLb (S.prob θ) (mixture S w) ≤ -logb 2 (w θ) := by
    intro θ
    have hterm : ∀ x, S.prob θ x * logb 2 (S.prob θ x / mixture S w x)
        ≤ S.prob θ x * (-logb 2 (w θ)) := by
      intro x
      refine mul_le_mul_of_nonneg_left ?_ (S.nonneg θ x)
      have hbound : S.prob θ x / mixture S w x ≤ 1 / w θ := by
        rw [div_le_div_iff₀ (hm x) (hw θ)]
        have hle : w θ * S.prob θ x ≤ mixture S w x := by
          unfold mixture
          refine Finset.single_le_sum (f := fun θ' => w θ' * S.prob θ' x)
            (fun θ' _ => (mul_pos (hw θ') (hp θ' x)).le) (mem_univ θ)
        linarith
      have := Real.logb_le_logb_of_le (b := 2) (by norm_num) (div_pos (hp θ x) (hm x)) hbound
      rw [one_div, Real.logb_inv] at this
      exact this
    calc KLb (S.prob θ) (mixture S w) ≤ ∑ x, S.prob θ x * (-logb 2 (w θ)) :=
          Finset.sum_le_sum fun x _ => hterm x
      _ = -logb 2 (w θ) := by rw [← Finset.sum_mul, S.sum_one θ, one_mul]
  unfold mutualInfo entropyb
  refine Finset.sum_le_sum fun θ _ => ?_
  have := mul_le_mul_of_nonneg_left (hKL θ) (hw θ).le
  calc w θ * KLb (S.prob θ) (mixture S w) ≤ w θ * -logb 2 (w θ) := this
    _ = -(w θ * logb 2 (w θ)) := by ring

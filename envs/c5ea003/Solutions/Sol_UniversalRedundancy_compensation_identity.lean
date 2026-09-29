-- Prove2me | solution 1 for UniversalRedundancy.compensation_identity
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T03:18:01.606506+00:00
-- url     : https://prove2.me/submissions/9c54bc0e-65a9-43dd-806a-e64faeeeee6b

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
theorem solution(w : Θ → ℝ) (q : X → ℝ) (hw : ∀ θ, 0 < w θ)
    (hp : ∀ θ x, 0 < S.prob θ x) (hq : ∀ x, 0 < q x) :
    bayesRedundancy S w q = mutualInfo S w + KLb (mixture S w) q := by
  have hm : ∀ x, 0 < mixture S w x := mixture_pos S w hw hp
  have hsplit : ∀ θ x, logb 2 (S.prob θ x / q x)
      = logb 2 (S.prob θ x / mixture S w x) + logb 2 (mixture S w x / q x) := by
    intro θ x
    have hmx : mixture S w x ≠ 0 := (hm x).ne'
    have hqx : q x ≠ 0 := (hq x).ne'
    have h1 : S.prob θ x / q x
        = (S.prob θ x / mixture S w x) * (mixture S w x / q x) := by
      field_simp
    rw [h1, Real.logb_mul (ne_of_gt (div_pos (hp θ x) (hm x)))
      (ne_of_gt (div_pos (hm x) (hq x)))]
  have hexpand : bayesRedundancy S w q
      = (∑ θ, w θ * ∑ x, S.prob θ x * logb 2 (S.prob θ x / mixture S w x))
        + ∑ θ, w θ * ∑ x, S.prob θ x * logb 2 (mixture S w x / q x) := by
    unfold bayesRedundancy KLb
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun θ _ => ?_
    rw [← mul_add, ← Finset.sum_add_distrib]
    refine congrArg (fun t => w θ * t) (Finset.sum_congr rfl fun x _ => ?_)
    rw [hsplit θ x, mul_add]
  have hsecond : ∑ θ, w θ * ∑ x, S.prob θ x * logb 2 (mixture S w x / q x)
      = KLb (mixture S w) q := by
    unfold KLb mixture
    calc ∑ θ, w θ * ∑ x, S.prob θ x * logb 2 ((∑ θ', w θ' * S.prob θ' x) / q x)
        = ∑ θ, ∑ x, w θ * S.prob θ x * logb 2 ((∑ θ', w θ' * S.prob θ' x) / q x) := by
          refine Finset.sum_congr rfl fun θ _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun x _ => by ring
      _ = ∑ x, ∑ θ, w θ * S.prob θ x * logb 2 ((∑ θ', w θ' * S.prob θ' x) / q x) :=
          Finset.sum_comm
      _ = ∑ x, (∑ θ, w θ * S.prob θ x) * logb 2 ((∑ θ', w θ' * S.prob θ' x) / q x) :=
          Finset.sum_congr rfl fun x _ => by rw [Finset.sum_mul]
  rw [hexpand, hsecond]
  rfl

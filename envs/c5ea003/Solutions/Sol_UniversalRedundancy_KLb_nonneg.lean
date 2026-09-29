-- Prove2me | solution 1 for UniversalRedundancy.KLb_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T02:03:19.973645+00:00
-- url     : https://prove2.me/submissions/d2217c2f-5a49-4c31-950f-1bc0b0a9059b

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






/-! ## Capacity never exceeds the worst-case price -/



/-! ## Capacity is at most the entropy of the prior -/




open UniversalRedundancy in
theorem solution(p q : X → ℝ) (hp : ∀ x, 0 < p x) (hq : ∀ x, 0 < q x)
    (hps : ∑ x, p x = 1) (hqs : ∑ x, q x = 1) : 0 ≤ KLb p q := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have key : ∑ x, p x * Real.log (q x / p x) ≤ 0 := by
    have hstep : ∀ x ∈ (univ : Finset X), p x * Real.log (q x / p x) ≤ q x - p x := by
      intro x _
      have hpx := hp x
      have hqx := hq x
      have hlt : Real.log (q x / p x) ≤ q x / p x - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      have hmul := mul_le_mul_of_nonneg_left hlt hpx.le
      calc p x * Real.log (q x / p x) ≤ p x * (q x / p x - 1) := hmul
        _ = q x - p x := by field_simp
    calc ∑ x, p x * Real.log (q x / p x) ≤ ∑ x, (q x - p x) := Finset.sum_le_sum hstep
      _ = 0 := by rw [Finset.sum_sub_distrib, hps, hqs, sub_self]
  have hflip : ∀ x, p x * logb 2 (p x / q x)
      = -(p x * Real.log (q x / p x)) / Real.log 2 := by
    intro x
    have hpx := hp x
    have hqx := hq x
    have hinv : (p x / q x) = (q x / p x)⁻¹ := by field_simp
    rw [logb, hinv, Real.log_inv]
    field_simp
  unfold KLb
  rw [Finset.sum_congr rfl fun x _ => hflip x, ← Finset.sum_div,
    Finset.sum_neg_distrib]
  exact div_nonneg (by linarith) hlog2.le

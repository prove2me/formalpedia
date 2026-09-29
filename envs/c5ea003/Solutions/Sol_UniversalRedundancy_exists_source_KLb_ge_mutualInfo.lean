-- Prove2me | solution 1 for UniversalRedundancy.exists_source_KLb_ge_mutualInfo
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T03:25:04.892162+00:00
-- url     : https://prove2.me/submissions/bcbfd17d-1963-4ecc-b999-a613a49e8188

-- Sol generated from MachineLearning/UniversalRedundancy/Capacity.lean
import Mathlib
import Definitions.Def_MachineLearning_UniversalRedundancy_Capacity
import Definitions.Def_MachineLearning_UniversalRedundancy_Core
import Theorems.Thm_UniversalRedundancy_KLb_nonneg
import Theorems.Thm_UniversalRedundancy_compensation_identity
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

omit [Nonempty Θ] in
lemma mixture_sum_one (w : Θ → ℝ) (hws : ∑ θ, w θ = 1) : ∑ x, mixture S w x = 1 := by
  unfold mixture
  rw [Finset.sum_comm]
  calc ∑ θ, ∑ x, w θ * S.prob θ x = ∑ θ, w θ * ∑ x, S.prob θ x :=
        Finset.sum_congr rfl fun θ _ => by rw [Finset.mul_sum]
    _ = ∑ θ, w θ := by simp [S.sum_one]
    _ = 1 := hws


/-- **The mixture code is Bayes optimal.**  No coding distribution achieves
average redundancy below the capacity functional `I(w)`. -/
theorem mutualInfo_le_bayesRedundancy (w : Θ → ℝ) (q : X → ℝ) (hw : ∀ θ, 0 < w θ)
    (hws : ∑ θ, w θ = 1) (hp : ∀ θ x, 0 < S.prob θ x) (hq : ∀ x, 0 < q x)
    (hqs : ∑ x, q x = 1) : mutualInfo S w ≤ bayesRedundancy S w q := by
  have hid := compensation_identity S w q hw hp hq
  have hnn : 0 ≤ KLb (mixture S w) q :=
    KLb_nonneg _ _ (mixture_pos S w hw hp) hq (mixture_sum_one S w hws) hqs
  linarith


/-! ## Capacity never exceeds the worst-case price -/



/-! ## Capacity is at most the entropy of the prior -/




open UniversalRedundancy in
theorem solution(w : Θ → ℝ) (q : X → ℝ) (hw : ∀ θ, 0 < w θ)
    (hws : ∑ θ, w θ = 1) (hp : ∀ θ x, 0 < S.prob θ x) (hq : ∀ x, 0 < q x)
    (hqs : ∑ x, q x = 1) : ∃ θ, mutualInfo S w ≤ KLb (S.prob θ) q := by
  by_contra hcon
  push_neg at hcon
  have hlt : ∑ θ, w θ * KLb (S.prob θ) q < ∑ θ, w θ * mutualInfo S w := by
    refine Finset.sum_lt_sum_of_nonempty ⟨Classical.arbitrary Θ, mem_univ _⟩ fun θ _ => ?_
    exact mul_lt_mul_of_pos_left (hcon θ) (hw θ)
  have hsum : ∑ θ, w θ * mutualInfo S w = mutualInfo S w := by
    rw [← Finset.sum_mul, hws, one_mul]
  have hbayes := mutualInfo_le_bayesRedundancy S w q hw hws hp hq hqs
  unfold bayesRedundancy at hbayes
  rw [hsum] at hlt
  linarith

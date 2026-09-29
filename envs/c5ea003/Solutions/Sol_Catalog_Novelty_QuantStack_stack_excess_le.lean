-- Prove2me | solution 1 for Catalog.Novelty.QuantStack.stack_excess_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T19:21:27.129552+00:00
-- url     : https://prove2.me/submissions/24cedc1c-5ae7-48c3-bbbc-175e54f0cb08

-- Sol generated from Novelty/QuantStackComposition.lean
import Mathlib
import Definitions.Def_Novelty_QuantCurvatureNoFloor
import Definitions.Def_Novelty_QuantStackComposition
import Theorems.Thm_Catalog_Novelty_QuantCurvature_quadExcess_nonneg
import Theorems.Thm_Catalog_Novelty_QuantStack_quadPair_sq_le

/-!
# Composing quantisation axes: the serving-stack budget is a seminorm

Cycle 2 of the NET-95 thread.  The practical claim attached to the measurement is
that a CPU serving stack composes independent compressions — `q4_k_m` weights
(+1.816%) with a K8/V4 cache (+0.14%) — and that the aggregate cost is "about the
sum".  This file proves what the curvature model actually licenses, which is
strictly stronger and quantitative.

In the second-order model of `Novelty.QuantCurvatureNoFloor`, the excess loss
`quadExcess lam e = ½ ∑ᵢ λᵢ eᵢ²` is the *square of a seminorm* in the
perturbation `e`.  Consequently:

* `quadExcess_sqrt_subadditive` / `quadExcess_add_le` — the triangle inequality:
  `√Q(e + f) ≤ √Q(e) + √Q(f)`.  Costs add in the square-root scale, never worse.
  (Proved from the discrete Cauchy–Schwarz inequality applied to the vectors
  `√λᵢ eᵢ` and `√λᵢ fᵢ`; degeneracy `λᵢ = 0` is allowed.)
* `stack_excess_le` — hence a two-axis budget: `Q ≤ a + b + 2√(ab)`.
* `cpu_stack_aggregate_bound` — instantiated at the measured numbers, the whole
  weight + cache stack is guaranteed to cost **under 3%** of perplexity, whatever
  the correlation between the two perturbations.
* `stack_excess_additive_of_orthogonal` — and if the two perturbations are
  orthogonal in the Hessian metric (the "independent noise" hypothesis), the cost
  is *exactly* additive.  With the measured numbers this predicts
  `1.816% + 0.14% = 1.956%`, versus the worst-case `2.97%`: a sharp, falsifiable
  prediction for the joint weight × cache arm that has not yet been run.
-/

open Catalog.Novelty.QuantStack

open Finset Catalog.Novelty.QuantCurvature

variable {n : ℕ}


/-- Expansion of the quadratic excess along a sum of perturbations. -/
theorem quadExcess_add_expand (lam e f : Fin n → ℝ) :
    quadExcess lam (e + f) = quadExcess lam e + quadExcess lam f + 2 * quadPair lam e f := by
  have key : ∑ i, lam i * (e i + f i) ^ 2
      = (∑ i, lam i * e i ^ 2) + (∑ i, lam i * f i ^ 2) + 2 * ∑ i, lam i * (e i * f i) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [quadExcess, quadPair, Pi.add_apply, key]
  ring








open Catalog.Novelty.QuantStack in
theorem solution(lam ew ec : Fin n → ℝ) (hlam : ∀ i, 0 ≤ lam i) (a b : ℝ)
    (hw : quadExcess lam ew ≤ a) (hc : quadExcess lam ec ≤ b) :
    quadExcess lam (ew + ec) ≤ a + b + 2 * Real.sqrt (a * b) := by
  have hne := quadExcess_nonneg lam ew hlam
  have hnf := quadExcess_nonneg lam ec hlam
  have ha : 0 ≤ a := le_trans hne hw
  have hb : 0 ≤ b := le_trans hnf hc
  have hexp := quadExcess_add_expand lam ew ec
  have hcs := quadPair_sq_le lam ew ec hlam
  have hpairle : quadPair lam ew ec ≤ Real.sqrt (a * b) := by
    have h1 : quadPair lam ew ec ≤ |quadPair lam ew ec| := le_abs_self _
    have h2 : |quadPair lam ew ec| ≤ Real.sqrt (a * b) := by
      rw [← Real.sqrt_sq_eq_abs]
      refine Real.sqrt_le_sqrt (le_trans hcs ?_)
      nlinarith [hne, hnf, hw, hc]
    linarith
  linarith [hexp, hpairle, hw, hc]

-- Prove2me | solution 1 for Catalog.Novelty.QuantStack.quadPair_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T19:18:53.402012+00:00
-- url     : https://prove2.me/submissions/d7212112-0103-4276-8da2-a14e71577b36

-- Sol generated from Novelty/QuantStackComposition.lean
import Mathlib
import Definitions.Def_Novelty_QuantCurvatureNoFloor
import Definitions.Def_Novelty_QuantStackComposition

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










open Catalog.Novelty.QuantStack in
theorem solution(lam e f : Fin n → ℝ) (hlam : ∀ i, 0 ≤ lam i) :
    quadPair lam e f ^ 2 ≤ quadExcess lam e * quadExcess lam f := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => Real.sqrt (lam i) * e i) (fun i => Real.sqrt (lam i) * f i)
  have hrw : ∀ (g : Fin n → ℝ), ∑ i, (Real.sqrt (lam i) * g i) ^ 2 = ∑ i, lam i * g i ^ 2 := by
    intro g
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_pow, Real.sq_sqrt (hlam i)]
  have hmix : ∑ i, (Real.sqrt (lam i) * e i) * (Real.sqrt (lam i) * f i)
      = ∑ i, lam i * (e i * f i) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    have : Real.sqrt (lam i) * Real.sqrt (lam i) = lam i :=
      Real.mul_self_sqrt (hlam i)
    calc (Real.sqrt (lam i) * e i) * (Real.sqrt (lam i) * f i)
        = (Real.sqrt (lam i) * Real.sqrt (lam i)) * (e i * f i) := by ring
      _ = lam i * (e i * f i) := by rw [this]
  rw [hmix, hrw e, hrw f] at hcs
  have h4 : (4 : ℝ) * (quadPair lam e f ^ 2) ≤ 4 * (quadExcess lam e * quadExcess lam f) := by
    simp only [quadPair, quadExcess]
    nlinarith [hcs]
  linarith

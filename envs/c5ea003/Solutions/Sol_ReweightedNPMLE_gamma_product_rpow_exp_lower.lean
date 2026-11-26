-- Prove2me | solution 1 for ReweightedNPMLE.gamma_product_rpow_exp_lower
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:02:17.3739+00:00
-- url     : https://prove2.me/submissions/61f5a1fd-352c-4592-97c6-aed11ff2111c

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Tactic
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_DirichletIndependence
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_Weights
import Theorems.Thm_ReweightedNPMLE_log_one_add_ge_sub_sq

/-!
# Injective change of variables for determinant moments

This file packages the precise area-formula step used by the paper's
determinant-moment argument.  If an injective differentiable map sends a
localized event into a probability density, its density-weighted Jacobian
has integral at most one.  A pointwise Jacobian/density comparison then
transfers that bound to the desired random variable.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

open ReweightedNPMLE
open ReweightedNPMLE in
/-- The logarithm inequality converts the product of multiplicative Gamma
density factors into the exponential cost used in the determinant moment. -/
theorem solution {n : ℕ} {α : ℝ} (hα : 0 ≤ α)
    (w t : Fin n → ℝ) (ht : ∀ i, |t i| ≤ 1 / 8) :
    Real.exp (-α * (∑ i, (w i - 1) * t i + ∑ i, (t i) ^ 2)) ≤
      (∏ i, (1 + t i) ^ α) * Real.exp (-α * ∑ i, w i * t i) := by
  have htpos (i : Fin n) : 0 < 1 + t i := by
    have hi := neg_le_of_abs_le (ht i)
    linarith
  have hlog : ∑ i, (t i - (t i) ^ 2) ≤ ∑ i, Real.log (1 + t i) :=
    Finset.sum_le_sum fun i _ ↦ log_one_add_ge_sub_sq (ht i)
  have hprod : (∏ i, (1 + t i) ^ α) =
      Real.exp (α * ∑ i, Real.log (1 + t i)) := by
    simp_rw [Real.rpow_def_of_pos (htpos _)]
    rw [← Real.exp_sum]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hprod, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hscaled : α * ∑ i, (t i - (t i) ^ 2) ≤
      α * ∑ i, Real.log (1 + t i) := mul_le_mul_of_nonneg_left hlog hα
  rw [Finset.sum_sub_distrib] at hscaled
  have hcost : ∑ i, (w i - 1) * t i =
      (∑ i, w i * t i) - ∑ i, t i := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hcost]
  linarith

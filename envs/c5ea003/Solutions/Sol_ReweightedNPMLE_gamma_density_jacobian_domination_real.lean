-- Prove2me | solution 1 for ReweightedNPMLE.gamma_density_jacobian_domination_real
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:03:00.370415+00:00
-- url     : https://prove2.me/submissions/84f91f62-5a7e-4e2a-b0f6-47325c2c0a2e

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
import Theorems.Thm_ReweightedNPMLE_gamma_product_rpow_exp_lower

-- Inline helpers preserved from ReweightedNPMLE.DirichletIndependence.
section
/-!
# Scale invariance behind Gamma--Dirichlet independence

The normalized Gamma vector is unchanged by a common positive rescaling.
This file first proves the corresponding exact scaling laws for scalar and
finite-product Gamma measures.  These are the measure-theoretic core of the
remaining independence statement in Proposition 2.1.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace ReweightedNPMLE

















/-- Scalar density ratio identity under the multiplicative displacement
`w ↦ w(1+t)`. -/
theorem gammaPDFReal_mul_one_add {α w t : ℝ}
    (hw : 0 < w) (ht : 0 < 1 + t) :
    gammaPDFReal α α (w * (1 + t)) =
      gammaPDFReal α α w * (1 + t) ^ (α - 1) *
        Real.exp (-α * w * t) := by
  simp only [gammaPDFReal, if_pos hw.le, if_pos (mul_pos hw ht).le]
  rw [Real.mul_rpow hw.le ht.le]
  have hexp : Real.exp (-(α * (w * (1 + t)))) =
      Real.exp (-(α * w)) * Real.exp (-α * w * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  ring

/-- Product-density ratio identity for the paper's coordinatewise
change-of-variables map. -/
theorem gammaProductDensityReal_mul_one_add {n : ℕ} {α : ℝ}
    (w t : Fin n → ℝ) (hw : ∀ i, 0 < w i) (ht : ∀ i, 0 < 1 + t i) :
    gammaProductDensityReal n α α (fun i ↦ w i * (1 + t i)) =
      gammaProductDensityReal n α α w *
        (∏ i, (1 + t i) ^ (α - 1)) *
          Real.exp (-α * ∑ i, w i * t i) := by
  unfold gammaProductDensityReal
  simp_rw [gammaPDFReal_mul_one_add (hw _) (ht _)]
  simp only [Finset.prod_mul_distrib]
  rw [← Real.exp_sum]
  congr 1
  rw [Finset.mul_sum]
  ring





























end ReweightedNPMLE
end

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
/-- Combining the product-Gamma density ratio, the logarithm lower bound,
and an assumed Jacobian lower bound gives the pointwise domination required
by the area formula. -/
theorem solution
    {n : ℕ} {α c J : ℝ} (hα : 0 < α) (hc : 0 ≤ c)
    (w t : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (ht : ∀ i, |t i| ≤ 1 / 8)
    (hdet : (∏ i, (1 + t i)) * c ≤ J) :
    gammaProductDensityReal n α α w *
        (c * Real.exp (-α *
          (∑ i, (w i - 1) * t i + ∑ i, (t i) ^ 2))) ≤
      J * gammaProductDensityReal n α α
        (fun i ↦ w i * (1 + t i)) := by
  have htpos (i : Fin n) : 0 < 1 + t i := by
    have hi := neg_le_of_abs_le (ht i)
    linarith
  have hp : 0 ≤ gammaProductDensityReal n α α w := by
    unfold gammaProductDensityReal
    exact Finset.prod_nonneg fun i _ ↦ gammaPDFReal_nonneg hα hα _
  have hB : 0 ≤ ∏ i, (1 + t i) ^ (α - 1) :=
    Finset.prod_nonneg fun i _ ↦ (Real.rpow_pos_of_pos (htpos i) _).le
  have hC : 0 ≤ Real.exp (-α * ∑ i, w i * t i) := (Real.exp_pos _).le
  have hAB : (∏ i, (1 + t i)) * (∏ i, (1 + t i) ^ (α - 1)) =
      ∏ i, (1 + t i) ^ α := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [Real.rpow_sub_one (htpos i).ne']
    field_simp [(htpos i).ne']
  have hlower := gamma_product_rpow_exp_lower hα.le w t ht
  rw [gammaProductDensityReal_mul_one_add w t hw htpos]
  calc
    gammaProductDensityReal n α α w *
        (c * Real.exp (-α *
          (∑ i, (w i - 1) * t i + ∑ i, (t i) ^ 2))) ≤
        gammaProductDensityReal n α α w *
          (c * ((∏ i, (1 + t i) ^ α) *
            Real.exp (-α * ∑ i, w i * t i))) := by gcongr
    _ = ((∏ i, (1 + t i)) * c) *
        (gammaProductDensityReal n α α w *
          (∏ i, (1 + t i) ^ (α - 1)) *
            Real.exp (-α * ∑ i, w i * t i)) := by rw [← hAB]; ring
    _ ≤ J * (gammaProductDensityReal n α α w *
          (∏ i, (1 + t i) ^ (α - 1)) *
            Real.exp (-α * ∑ i, w i * t i)) := by
      exact mul_le_mul_of_nonneg_right hdet (mul_nonneg (mul_nonneg hp hB) hC)

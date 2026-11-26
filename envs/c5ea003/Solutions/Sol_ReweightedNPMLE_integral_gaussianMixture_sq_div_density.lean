-- Prove2me | solution 1 for ReweightedNPMLE.integral_gaussianMixture_sq_div_density
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:07:22.839921+00:00
-- url     : https://prove2.me/submissions/84a3dac5-f097-44d4-bcbb-1ae3761a8586

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic
import Definitions.Def_ReweightedNPMLE_Gaussian
import Definitions.Def_ReweightedNPMLE_GaussianMixtureMeasure
import Theorems.Thm_ReweightedNPMLE_gaussianMixture_sq_div_density_integrable_prod
import Theorems.Thm_ReweightedNPMLE_integral_gaussianMixture_mul_kernel_div_density

-- Inline helpers preserved from ReweightedNPMLE.Gaussian.
section
/-!
# Gaussian location-mixture algebra

The manuscript factors a Gaussian translate into a common density and an exponential
score.  This file formalizes that identity and the uniform score bounds used in both the
effective-dimension and finite-net arguments.
-/

open scoped BigOperators RealInnerProductSpace
open MeasureTheory

namespace ReweightedNPMLE































/-- The Gaussian translation identity used in Sections 3 and 4 of the manuscript. -/
theorem gaussianKernel_eq_density_mul_exp_score {d : ℕ} (x θ : Point d) :
    gaussianKernel d x θ = gaussianDensity d x * Real.exp (gaussianScore x θ) := by
  rw [gaussianKernel, gaussianDensity, gaussianScore, mul_assoc, ← Real.exp_add]
  congr 1
  rw [norm_sub_sq_real]
  ring































end ReweightedNPMLE
end

/-!
# Gaussian mixtures indexed by probability measures

This module connects the finite-sum Gaussian algebra to the paper's original
parameter space of arbitrary compactly supported mixing laws.
-/

open scoped BigOperators RealInnerProductSpace
open MeasureTheory

open ReweightedNPMLE
open ReweightedNPMLE in
theorem solution
    {d : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) [IsProbabilityMeasure μ]
    (θ : Θ → Point d) (hθmeas : Measurable θ)
    {S : ℝ} (hS : 0 ≤ S) (hθS : ∀ a, ‖θ a‖ ≤ S) :
    ∫ x : Point d, (gaussianMixture μ θ x) ^ 2 / gaussianDensity d x =
      ∫ a, ∫ b, Real.exp (inner ℝ (θ b) (θ a)) ∂μ ∂μ := by
  have hprod := gaussianMixture_sq_div_density_integrable_prod
    μ θ hθmeas hS hθS
  calc
    (∫ x : Point d, (gaussianMixture μ θ x) ^ 2 / gaussianDensity d x) =
        ∫ x : Point d, ∫ a,
          gaussianMixture μ θ x * Real.exp (gaussianScore x (θ a)) ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦ by
        change (gaussianMixture μ θ x) ^ 2 / gaussianDensity d x =
          ∫ a, gaussianMixture μ θ x * Real.exp (gaussianScore x (θ a)) ∂μ
        have hmix : gaussianMixture μ θ x = gaussianDensity d x *
            ∫ a, Real.exp (gaussianScore x (θ a)) ∂μ := by
          unfold gaussianMixture
          simp_rw [gaussianKernel_eq_density_mul_exp_score]
          exact integral_const_mul _ _
        rw [integral_const_mul, hmix]
        field_simp [(gaussianDensity_pos d x).ne']
    _ = ∫ a, ∫ x : Point d,
        gaussianMixture μ θ x * Real.exp (gaussianScore x (θ a)) ∂volume ∂μ := by
      exact (integral_integral_swap hprod).symm
    _ = ∫ a, ∫ b, Real.exp (inner ℝ (θ b) (θ a)) ∂μ ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun a ↦ by
        change (∫ x : Point d,
            gaussianMixture μ θ x * Real.exp (gaussianScore x (θ a))) =
          ∫ b, Real.exp (inner ℝ (θ b) (θ a)) ∂μ
        rw [show (∫ x : Point d,
            gaussianMixture μ θ x * Real.exp (gaussianScore x (θ a))) =
            ∫ x : Point d,
              gaussianMixture μ θ x * gaussianKernel d x (θ a) /
                gaussianDensity d x by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun x ↦ by
            change gaussianMixture μ θ x * Real.exp (gaussianScore x (θ a)) =
              gaussianMixture μ θ x * gaussianKernel d x (θ a) /
                gaussianDensity d x
            rw [gaussianKernel_eq_density_mul_exp_score]
            field_simp [(gaussianDensity_pos d x).ne']]
        exact integral_gaussianMixture_mul_kernel_div_density
          μ θ hθmeas hS hθS (θ a) (hθS a)

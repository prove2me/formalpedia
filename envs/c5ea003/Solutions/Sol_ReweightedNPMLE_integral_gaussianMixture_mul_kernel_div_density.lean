-- Prove2me | solution 1 for ReweightedNPMLE.integral_gaussianMixture_mul_kernel_div_density
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:05:44.276978+00:00
-- url     : https://prove2.me/submissions/85a66d11-2062-4151-9e48-982d8597ad6d

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic
import Definitions.Def_ReweightedNPMLE_Gaussian
import Definitions.Def_ReweightedNPMLE_GaussianMixtureMeasure
import Theorems.Thm_ReweightedNPMLE_gaussianKernel_product_div_density_comp_integrable_prod
import Theorems.Thm_ReweightedNPMLE_integral_gaussianKernel_product_div_density

/-!
# Gaussian mixtures indexed by probability measures

This module connects the finite-sum Gaussian algebra to the paper's original
parameter space of arbitrary compactly supported mixing laws.
-/

open scoped BigOperators RealInnerProductSpace
open MeasureTheory

open ReweightedNPMLE
open ReweightedNPMLE in
/-- Mixing the first argument of the Gaussian overlap identity commutes with
integration. -/
theorem solution
    {d : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) [IsProbabilityMeasure μ]
    (θ : Θ → Point d) (hθmeas : Measurable θ)
    {S : ℝ} (hS : 0 ≤ S) (hθS : ∀ a, ‖θ a‖ ≤ S)
    (η : Point d) (hηS : ‖η‖ ≤ S) :
    ∫ x : Point d,
        gaussianMixture μ θ x * gaussianKernel d x η / gaussianDensity d x =
      ∫ a, Real.exp (inner ℝ (θ a) η) ∂μ := by
  have hprod := gaussianKernel_product_div_density_comp_integrable_prod
    μ θ hθmeas hS hθS η hηS
  unfold gaussianMixture
  calc
    (∫ x : Point d,
        (∫ a, gaussianKernel d x (θ a) ∂μ) * gaussianKernel d x η /
          gaussianDensity d x) =
        ∫ x : Point d, ∫ a,
          gaussianKernel d x (θ a) * gaussianKernel d x η /
            gaussianDensity d x ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x ↦ by
        change (∫ a, gaussianKernel d x (θ a) ∂μ) *
            gaussianKernel d x η / gaussianDensity d x =
          ∫ a, gaussianKernel d x (θ a) * gaussianKernel d x η /
            gaussianDensity d x ∂μ
        rw [show (∫ a, gaussianKernel d x (θ a) ∂μ) *
            gaussianKernel d x η / gaussianDensity d x =
            (∫ a, gaussianKernel d x (θ a) ∂μ) *
              (gaussianKernel d x η / gaussianDensity d x) by ring]
        rw [← integral_mul_const]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun a ↦ by ring
    _ = ∫ a, ∫ x : Point d,
        gaussianKernel d x (θ a) * gaussianKernel d x η /
          gaussianDensity d x ∂volume ∂μ := by
      exact (integral_integral_swap hprod).symm
    _ = ∫ a, Real.exp (inner ℝ (θ a) η) ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun a ↦
        integral_gaussianKernel_product_div_density (θ a) η

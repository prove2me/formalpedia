-- Prove2me | solution 1 for ReweightedNPMLE.gaussianMixture_mul_kernel_div_density_integrable
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:05:42.675838+00:00
-- url     : https://prove2.me/submissions/d060b70d-aa85-431d-9f51-e9848a7da1a3

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
    {S : ℝ} (hS : 0 ≤ S) (hθS : ∀ a, ‖θ a‖ ≤ S)
    (η : Point d) (hηS : ‖η‖ ≤ S) :
    Integrable (fun x : Point d ↦
      gaussianMixture μ θ x * gaussianKernel d x η / gaussianDensity d x) := by
  have hprod := gaussianKernel_product_div_density_comp_integrable_prod
    μ θ hθmeas hS hθS η hηS
  apply hprod.integral_prod_right.congr
  exact Filter.Eventually.of_forall fun x ↦ by
    unfold gaussianMixture
    change (∫ a, gaussianKernel d x (θ a) * gaussianKernel d x η /
        gaussianDensity d x ∂μ) =
      (∫ a, gaussianKernel d x (θ a) ∂μ) *
        gaussianKernel d x η / gaussianDensity d x
    symm
    rw [show (∫ a, gaussianKernel d x (θ a) ∂μ) *
        gaussianKernel d x η / gaussianDensity d x =
        (∫ a, gaussianKernel d x (θ a) ∂μ) *
          (gaussianKernel d x η / gaussianDensity d x) by ring]
    rw [← integral_mul_const]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun a ↦ by ring

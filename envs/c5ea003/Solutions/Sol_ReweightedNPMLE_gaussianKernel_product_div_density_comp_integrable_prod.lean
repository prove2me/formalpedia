-- Prove2me | solution 1 for ReweightedNPMLE.gaussianKernel_product_div_density_comp_integrable_prod
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:04:53.247719+00:00
-- url     : https://prove2.me/submissions/83d7e8f2-e505-4c55-85ef-43c698e35dd5

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic
import Definitions.Def_ReweightedNPMLE_Gaussian
import Definitions.Def_ReweightedNPMLE_GaussianMixtureMeasure
import Theorems.Thm_ReweightedNPMLE_exp_inner_comp_integrable
import Theorems.Thm_ReweightedNPMLE_gaussianKernel_product_div_density
import Theorems.Thm_ReweightedNPMLE_integral_gaussianKernel_product_div_density

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

















































/-- The Gaussian overlap integrand is integrable. -/
theorem gaussianKernel_product_div_density_integrable
    {d : ℕ} (θ η : Point d) :
    Integrable (fun x ↦
      gaussianKernel d x θ * gaussianKernel d x η / gaussianDensity d x) := by
  apply ((gaussianDensity_integrable d).comp_sub_right (θ + η)).const_mul
    (Real.exp (inner ℝ θ η)) |>.congr
  exact Filter.Eventually.of_forall fun x ↦
    (gaussianKernel_product_div_density x θ η).symm













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
    {S : ℝ} (hS : 0 ≤ S) (hθS : ∀ a, ‖θ a‖ ≤ S)
    (η : Point d) (hηS : ‖η‖ ≤ S) :
    Integrable (fun z : Θ × Point d ↦
      gaussianKernel d z.2 (θ z.1) * gaussianKernel d z.2 η /
        gaussianDensity d z.2) (μ.prod volume) := by
  have hmeas : AEStronglyMeasurable (fun z : Θ × Point d ↦
      gaussianKernel d z.2 (θ z.1) * gaussianKernel d z.2 η /
        gaussianDensity d z.2) (μ.prod volume) := by
    have hg : AEStronglyMeasurable (fun z : Θ × Point d ↦
        Real.exp (inner ℝ (θ z.1) η) *
          gaussianDensity d (z.2 - (θ z.1 + η))) (μ.prod volume) := by
      have hθfst : Measurable (fun z : Θ × Point d ↦ θ z.1) :=
        hθmeas.comp measurable_fst
      have hinner : Measurable (fun z : Θ × Point d ↦
          inner ℝ (θ z.1) η) :=
        continuous_inner.measurable.comp (hθfst.prodMk measurable_const)
      have hexp : Measurable (fun z : Θ × Point d ↦
          Real.exp (inner ℝ (θ z.1) η)) :=
        Real.continuous_exp.measurable.comp hinner
      have harg : Measurable (fun z : Θ × Point d ↦
          z.2 - (θ z.1 + η)) :=
        measurable_snd.sub (hθfst.add measurable_const)
      exact (hexp.mul ((continuous_gaussianDensity d).measurable.comp harg)).aestronglyMeasurable
    apply hg.congr
    exact Filter.Eventually.of_forall fun z ↦
      (gaussianKernel_product_div_density z.2 (θ z.1) η).symm
  rw [integrable_prod_iff hmeas]
  constructor
  · exact Filter.Eventually.of_forall fun a ↦
      gaussianKernel_product_div_density_integrable (θ a) η
  · have hfun : (fun a : Θ ↦ ∫ x : Point d,
        ‖gaussianKernel d x (θ a) * gaussianKernel d x η /
          gaussianDensity d x‖) =
        fun a ↦ Real.exp (inner ℝ (θ a) η) := by
      funext a
      have hpos : ∀ x : Point d,
          0 < gaussianKernel d x (θ a) * gaussianKernel d x η /
            gaussianDensity d x := fun x ↦
        div_pos (mul_pos (gaussianKernel_pos d x (θ a))
          (gaussianKernel_pos d x η)) (gaussianDensity_pos d x)
      simp_rw [Real.norm_eq_abs, abs_of_pos (hpos _)]
      exact integral_gaussianKernel_product_div_density (θ a) η
    rw [hfun]
    exact exp_inner_comp_integrable μ θ hθmeas hS hθS η hηS

-- Prove2me | solution 1 for ReweightedNPMLE.gaussianMixture_sq_div_density_integrable_prod
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:06:28.352105+00:00
-- url     : https://prove2.me/submissions/b7cee1d4-f6a2-4668-9c89-0d71c385ee55

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic
import Definitions.Def_ReweightedNPMLE_Gaussian
import Definitions.Def_ReweightedNPMLE_GaussianMixtureMeasure
import Theorems.Thm_ReweightedNPMLE_exp_inner_comp_comp_integrable
import Theorems.Thm_ReweightedNPMLE_gaussianKernel_comp_integrable_prod
import Theorems.Thm_ReweightedNPMLE_gaussianMixture_mul_kernel_div_density_integrable
import Theorems.Thm_ReweightedNPMLE_gaussianMixture_pos
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



















theorem continuous_gaussianScore (d : ℕ) :
    Continuous fun z : Point d × Point d ↦ gaussianScore z.1 z.2 := by
  unfold gaussianScore
  fun_prop











/-- The Gaussian translation identity used in Sections 3 and 4 of the manuscript. -/
theorem gaussianKernel_eq_density_mul_exp_score {d : ℕ} (x θ : Point d) :
    gaussianKernel d x θ = gaussianDensity d x * Real.exp (gaussianScore x θ) := by
  rw [gaussianKernel, gaussianDensity, gaussianScore, mul_assoc, ← Real.exp_add]
  congr 1
  rw [norm_sub_sq_real]
  ring































end ReweightedNPMLE
end

-- Inline helpers preserved from ReweightedNPMLE.GaussianMixtureMeasure.
section
/-!
# Gaussian mixtures indexed by probability measures

This module connects the finite-sum Gaussian algebra to the paper's original
parameter space of arbitrary compactly supported mixing laws.
-/

open scoped BigOperators RealInnerProductSpace
open MeasureTheory

namespace ReweightedNPMLE









theorem gaussianMixture_integrable
    {d : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) [IsProbabilityMeasure μ]
    (θ : Θ → Point d) (hθ : Measurable θ) :
    Integrable (gaussianMixture μ θ) := by
  exact (gaussianKernel_comp_integrable_prod μ θ hθ).integral_prod_right

























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
    Integrable (fun z : Θ × Point d ↦
      gaussianMixture μ θ z.2 *
        Real.exp (gaussianScore z.2 (θ z.1))) (μ.prod volume) := by
  have hp := gaussianMixture_integrable μ θ hθmeas
  have hscore : Measurable (fun z : Θ × Point d ↦
      Real.exp (gaussianScore z.2 (θ z.1))) :=
    Real.continuous_exp.measurable.comp
      ((continuous_gaussianScore d).measurable.comp
        (measurable_snd.prodMk (hθmeas.comp measurable_fst)))
  have hmeas : AEStronglyMeasurable (fun z : Θ × Point d ↦
      gaussianMixture μ θ z.2 *
        Real.exp (gaussianScore z.2 (θ z.1))) (μ.prod volume) :=
    hp.aestronglyMeasurable.comp_snd.mul hscore.aestronglyMeasurable
  rw [integrable_prod_iff hmeas]
  constructor
  · exact Filter.Eventually.of_forall fun a ↦ by
      apply (gaussianMixture_mul_kernel_div_density_integrable
        μ θ hθmeas hS hθS (θ a) (hθS a)).congr
      exact Filter.Eventually.of_forall fun x ↦ by
        change gaussianMixture μ θ x * gaussianKernel d x (θ a) /
            gaussianDensity d x =
          gaussianMixture μ θ x * Real.exp (gaussianScore x (θ a))
        rw [gaussianKernel_eq_density_mul_exp_score]
        field_simp [(gaussianDensity_pos d x).ne']
  · have hdouble := exp_inner_comp_comp_integrable μ θ hθmeas hS hθS
    apply hdouble.integral_prod_right.congr
    exact Filter.Eventually.of_forall fun a ↦ by
      change (∫ b, Real.exp (inner ℝ (θ b) (θ a)) ∂μ) =
        ∫ x : Point d,
          ‖gaussianMixture μ θ x * Real.exp (gaussianScore x (θ a))‖
      symm
      rw [show (∫ x : Point d,
          ‖gaussianMixture μ θ x * Real.exp (gaussianScore x (θ a))‖) =
          ∫ x : Point d,
            gaussianMixture μ θ x * gaussianKernel d x (θ a) /
              gaussianDensity d x by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x ↦ by
          change ‖gaussianMixture μ θ x * Real.exp (gaussianScore x (θ a))‖ =
            gaussianMixture μ θ x * gaussianKernel d x (θ a) /
              gaussianDensity d x
          rw [Real.norm_eq_abs, abs_of_pos (mul_pos
            (gaussianMixture_pos μ θ hθmeas x) (Real.exp_pos _)),
            gaussianKernel_eq_density_mul_exp_score]
          field_simp [(gaussianDensity_pos d x).ne']]
      exact integral_gaussianMixture_mul_kernel_div_density
        μ θ hθmeas hS hθS (θ a) (hθS a)

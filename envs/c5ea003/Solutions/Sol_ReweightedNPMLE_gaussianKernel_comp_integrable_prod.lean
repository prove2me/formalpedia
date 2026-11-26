-- Prove2me | solution 1 for ReweightedNPMLE.gaussianKernel_comp_integrable_prod
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:02:46.956704+00:00
-- url     : https://prove2.me/submissions/2595ed6f-8366-4819-95fe-63f63004595a

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic
import Definitions.Def_ReweightedNPMLE_Gaussian
import Definitions.Def_ReweightedNPMLE_GaussianMixtureMeasure

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





































/-- Every translated Gaussian kernel is integrable. -/
theorem gaussianKernel_integrable (d : ℕ) (θ : Point d) :
    Integrable (fun x ↦ gaussianKernel d x θ) := by
  change Integrable (fun x ↦ gaussianDensity d (x - θ))
  exact (gaussianDensity_integrable d).comp_sub_right θ

/-- Every translated Gaussian kernel integrates to one. -/
theorem integral_gaussianKernel (d : ℕ) (θ : Point d) :
    ∫ x : Point d, gaussianKernel d x θ = 1 := by
  change (∫ x : Point d, gaussianDensity d (x - θ)) = 1
  rw [integral_sub_right_eq_self, integral_gaussianDensity]























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
/-- Joint integrability of a probability mixture kernel over parameter and
observation space. -/
theorem solution
    {d : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) [IsProbabilityMeasure μ]
    (θ : Θ → Point d) (hθ : Measurable θ) :
    Integrable (fun z : Θ × Point d ↦ gaussianKernel d z.2 (θ z.1))
      (μ.prod volume) := by
  have hmeas : AEStronglyMeasurable
      (fun z : Θ × Point d ↦ gaussianKernel d z.2 (θ z.1))
      (μ.prod volume) :=
    ((continuous_gaussianKernel d).measurable.comp
      (measurable_snd.prodMk (hθ.comp measurable_fst))).aestronglyMeasurable
  rw [integrable_prod_iff hmeas]
  constructor
  · exact Filter.Eventually.of_forall fun a ↦ gaussianKernel_integrable d (θ a)
  · have hfun : (fun a : Θ ↦
        ∫ x : Point d, ‖gaussianKernel d x (θ a)‖) = fun _ ↦ (1 : ℝ) := by
      funext a
      simp_rw [Real.norm_of_nonneg (gaussianKernel_pos d _ _).le]
      exact integral_gaussianKernel d (θ a)
    rw [hfun]
    exact integrable_const 1

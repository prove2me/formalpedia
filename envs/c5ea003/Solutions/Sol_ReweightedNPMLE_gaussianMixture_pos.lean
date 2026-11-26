-- Prove2me | solution 1 for ReweightedNPMLE.gaussianMixture_pos
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:52:41.066277+00:00
-- url     : https://prove2.me/submissions/26032a16-e061-4013-8fbf-7b3d686cda33

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic
import Definitions.Def_ReweightedNPMLE_Gaussian
import Definitions.Def_ReweightedNPMLE_GaussianMixtureMeasure

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
    (θ : Θ → Point d) (hθ : Measurable θ) (x : Point d) :
    0 < gaussianMixture μ θ x := by
  unfold gaussianMixture
  let f : Θ → ℝ := fun a ↦
    Real.log (gaussianKernel d x (θ a))
  have hfint : Integrable (fun a ↦ Real.exp (f a)) μ := by
    apply (gaussianKernel_comp_integrable μ θ hθ x).congr
    exact Filter.Eventually.of_forall fun a ↦ by
      dsimp [f]
      rw [Real.exp_log (gaussianKernel_pos d x (θ a))]
  have hpos := integral_exp_pos hfint
  calc
    0 < ∫ a, Real.exp (f a) ∂μ := hpos
    _ = ∫ a, gaussianKernel d x (θ a) ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun a ↦ by
        dsimp [f]
        rw [Real.exp_log (gaussianKernel_pos d x (θ a))]

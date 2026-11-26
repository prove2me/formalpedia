-- Prove2me | solution 1 for ReweightedNPMLE.continuous_gaussianMixture
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:02:26.337848+00:00
-- url     : https://prove2.me/submissions/6f53731c-3442-4624-b499-8fc967149aac

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
/-- Every Gaussian location mixture is continuous in its observation
argument.  The Gaussian bound supplies an integrable dominator for an
arbitrary probability mixing law. -/
theorem solution
    {d : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) [IsProbabilityMeasure μ]
    (θ : Θ → Point d) (hθ : Measurable θ) :
    Continuous (gaussianMixture μ θ) := by
  unfold gaussianMixture
  apply continuous_of_dominated (bound := fun _ ↦ gaussianConstant d)
  · intro x
    exact (gaussianKernel_comp_integrable μ θ hθ x).aestronglyMeasurable
  · intro x
    exact Filter.Eventually.of_forall fun a ↦ by
      rw [Real.norm_of_nonneg (gaussianKernel_pos d x (θ a)).le]
      exact gaussianKernel_le_constant x (θ a)
  · exact integrable_const _
  · exact Filter.Eventually.of_forall fun a ↦ by
      unfold gaussianKernel
      fun_prop

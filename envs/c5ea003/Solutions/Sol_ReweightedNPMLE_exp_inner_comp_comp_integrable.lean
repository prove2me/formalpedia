-- Prove2me | solution 1 for ReweightedNPMLE.exp_inner_comp_comp_integrable
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:03:27.006599+00:00
-- url     : https://prove2.me/submissions/fde45856-a16d-4ac8-9fda-8e8102c63a28

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
    (θ : Θ → Point d) (hθmeas : Measurable θ)
    {S : ℝ} (hS : 0 ≤ S) (hθS : ∀ a, ‖θ a‖ ≤ S) :
    Integrable (fun z : Θ × Θ ↦ Real.exp (inner ℝ (θ z.1) (θ z.2)))
      (μ.prod μ) := by
  apply Integrable.of_bound
    (by fun_prop : AEStronglyMeasurable
      (fun z : Θ × Θ ↦ Real.exp (inner ℝ (θ z.1) (θ z.2))) (μ.prod μ))
    (Real.exp (S ^ 2))
  exact Filter.Eventually.of_forall fun z ↦ by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    calc
      inner ℝ (θ z.1) (θ z.2) ≤
          |inner ℝ (θ z.1) (θ z.2)| := le_abs_self _
      _ ≤ ‖θ z.1‖ * ‖θ z.2‖ := abs_real_inner_le_norm _ _
      _ ≤ S * S := mul_le_mul (hθS z.1) (hθS z.2) (norm_nonneg _) hS
      _ = S ^ 2 := by ring

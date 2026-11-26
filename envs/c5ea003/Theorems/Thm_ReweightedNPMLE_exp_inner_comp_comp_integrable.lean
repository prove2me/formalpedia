-- Prove2me | Theorems.Thm_ReweightedNPMLE_exp_inner_comp_comp_integrable
-- name    : ReweightedNPMLE.exp_inner_comp_comp_integrable
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:40:17.022303+00:00
-- url     : https://prove2.me/theorems/887b5476-38f1-5970-a62b-23aaaa88df16
-- title:
--   Joint integrability of the exponential inner-product kernel
-- statement:
--   Let \(\mu\) be a probability measure, let \(\theta:\Theta\to\mathbb R^d\) be measurable, and assume \(S\ge0\) with \(\|\theta(a)\|\le S\) for every \(a\). Then
--   \[
--   (a,b)\longmapsto e^{\langle\theta(a),\theta(b)\rangle}
--   \]
--   is integrable under \(\mu\otimes\mu\). Its absolute value is uniformly at most \(e^{S^2}\). The result justifies double integrals of the exponential kernel associated with a bounded-location Gaussian mixture.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GaussianMixtureMeasure.lean#L153-L172

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

theorem ReweightedNPMLE.exp_inner_comp_comp_integrable
    {d : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) [IsProbabilityMeasure μ]
    (θ : Θ → Point d) (hθmeas : Measurable θ)
    {S : ℝ} (hS : 0 ≤ S) (hθS : ∀ a, ‖θ a‖ ≤ S) :
    Integrable (fun z : Θ × Θ ↦ Real.exp (inner ℝ (θ z.1) (θ z.2)))
      (μ.prod μ) := by sorry

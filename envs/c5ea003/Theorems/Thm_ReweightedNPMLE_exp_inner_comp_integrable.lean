-- Prove2me | Theorems.Thm_ReweightedNPMLE_exp_inner_comp_integrable
-- name    : ReweightedNPMLE.exp_inner_comp_integrable
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:39:59.204711+00:00
-- url     : https://prove2.me/theorems/ff00c5f4-b175-47c5-8e69-f7db48c2a5e7
-- title:
--   Integrability of a bounded-location exponential overlap
-- statement:
--   Let \(\mu\) be a probability measure and let \(\theta:\Theta\to\mathbb R^d\) be measurable. Suppose \(S\ge0\), \(\|\theta(a)\|\le S\) for all \(a\), and \(\|\eta\|\le S\). Then
--   \[
--   a\longmapsto e^{\langle\theta(a),\eta\rangle}
--   \]
--   is integrable with respect to \(\mu\). In fact its absolute value is bounded everywhere by \(e^{S^2}\). This provides an integrable mixing-space expression for Gaussian overlap integrals.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GaussianMixtureMeasure.lean#L133-L151

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

theorem ReweightedNPMLE.exp_inner_comp_integrable
    {d : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) [IsProbabilityMeasure μ]
    (θ : Θ → Point d) (hθmeas : Measurable θ)
    {S : ℝ} (hS : 0 ≤ S) (hθS : ∀ a, ‖θ a‖ ≤ S)
    (η : Point d) (hηS : ‖η‖ ≤ S) :
    Integrable (fun a ↦ Real.exp (inner ℝ (θ a) η)) μ := by sorry

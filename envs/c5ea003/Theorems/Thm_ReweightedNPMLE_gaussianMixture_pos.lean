-- Prove2me | Theorems.Thm_ReweightedNPMLE_gaussianMixture_pos
-- name    : ReweightedNPMLE.gaussianMixture_pos
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:35:54.388844+00:00
-- url     : https://prove2.me/theorems/61bf1e8b-b494-4952-840f-05f21e0d8c86
-- title:
--   Strict positivity of arbitrary Gaussian probability mixtures
-- statement:
--   Let \(\mu\) be a probability measure on a measurable space \(\Theta\), let \(\theta:\Theta\to\mathbb R^d\) be measurable, and write \(\phi_d(x)=(2\pi)^{-d/2}e^{-\|x\|^2/2}\) and \(p(x)=\int\phi_d(x-\theta(a))\,d\mu(a)\). For every \(x\in\mathbb R^d\), one has \(p(x)>0\). This is strict pointwise positivity, without a bounded-support assumption or a uniform positive lower bound over all observation points. It ensures that ordinary log densities and ratios with denominator \(p(x)\) are well defined.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GaussianMixtureMeasure.lean#L111-L131

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

theorem ReweightedNPMLE.gaussianMixture_pos
    {d : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) [IsProbabilityMeasure μ]
    (θ : Θ → Point d) (hθ : Measurable θ) (x : Point d) :
    0 < gaussianMixture μ θ x := by sorry

-- Prove2me | Theorems.Thm_ReweightedNPMLE_continuous_gaussianMixture
-- name    : ReweightedNPMLE.continuous_gaussianMixture
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:39:35.674936+00:00
-- url     : https://prove2.me/theorems/06bf8280-5c99-59d6-94b4-62c919fc3b11
-- title:
--   Continuity of arbitrary Gaussian probability mixtures
-- statement:
--   Let \(\mu\) be a probability measure on a measurable space \(\Theta\), let \(\theta:\Theta\to\mathbb R^d\) be measurable, and write \(\phi_d(x)=(2\pi)^{-d/2}e^{-\|x\|^2/2}\) and \(p(x)=\int\phi_d(x-\theta(a))\,d\mu(a)\). Then \(p:\mathbb R^d\to\mathbb R\) is continuous. The conclusion holds for an arbitrary probability mixing measure and a measurable parameter map, even when the image of \(\theta\) is unbounded. In particular, compact support and finiteness of moments are unnecessary for continuity of the unit-covariance Gaussian mixture density.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GaussianMixtureMeasure.lean#L73-L92

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

theorem ReweightedNPMLE.continuous_gaussianMixture
    {d : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) [IsProbabilityMeasure μ]
    (θ : Θ → Point d) (hθ : Measurable θ) :
    Continuous (gaussianMixture μ θ) := by sorry

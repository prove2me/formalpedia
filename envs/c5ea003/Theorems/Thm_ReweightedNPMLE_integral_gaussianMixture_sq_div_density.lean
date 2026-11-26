-- Prove2me | Theorems.Thm_ReweightedNPMLE_integral_gaussianMixture_sq_div_density
-- name    : ReweightedNPMLE.integral_gaussianMixture_sq_div_density
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:42:37.021874+00:00
-- url     : https://prove2.me/theorems/f60773f3-74be-5675-a99f-44ab0cc74628
-- title:
--   Exponential-kernel formula for a Gaussian mixture’s weighted norm
-- statement:
--   Let \(\mu\) be a probability measure on a measurable space \(\Theta\), let \(\theta:\Theta\to\mathbb R^d\) be measurable, and write \(\phi_d(x)=(2\pi)^{-d/2}e^{-\|x\|^2/2}\) and \(p(x)=\int\phi_d(x-\theta(a))\,d\mu(a)\). Assume \(S\ge0\) and \(\|\theta(a)\|\le S\) for every \(a\). Then
--   \[
--   \int_{\mathbb R^d}\frac{p(x)^2}{\phi_d(x)}\,dx
--   =\int_\Theta\int_\Theta
--   e^{\langle\theta(b),\theta(a)\rangle}\,d\mu(b)\,d\mu(a).
--   \]
--   Both sides are finite. The weighted squared density norm is therefore the quadratic form of the exponential inner-product kernel evaluated at the mixing law.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GaussianMixtureMeasure.lean#L368-L414

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

theorem ReweightedNPMLE.integral_gaussianMixture_sq_div_density
    {d : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) [IsProbabilityMeasure μ]
    (θ : Θ → Point d) (hθmeas : Measurable θ)
    {S : ℝ} (hS : 0 ≤ S) (hθS : ∀ a, ‖θ a‖ ≤ S) :
    ∫ x : Point d, (gaussianMixture μ θ x) ^ 2 / gaussianDensity d x =
      ∫ a, ∫ b, Real.exp (inner ℝ (θ b) (θ a)) ∂μ ∂μ := by sorry

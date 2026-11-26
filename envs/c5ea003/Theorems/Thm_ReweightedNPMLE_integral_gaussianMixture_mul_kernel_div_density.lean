-- Prove2me | Theorems.Thm_ReweightedNPMLE_integral_gaussianMixture_mul_kernel_div_density
-- name    : ReweightedNPMLE.integral_gaussianMixture_mul_kernel_div_density
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:41:37.25438+00:00
-- url     : https://prove2.me/theorems/9e613613-f7c8-5eca-849b-e5206a376ab2
-- title:
--   Gaussian overlap identity with one general mixing law
-- statement:
--   Let \(\mu\) be a probability measure on a measurable space \(\Theta\), let \(\theta:\Theta\to\mathbb R^d\) be measurable, and write \(\phi_d(x)=(2\pi)^{-d/2}e^{-\|x\|^2/2}\) and \(p(x)=\int\phi_d(x-\theta(a))\,d\mu(a)\). Assume \(S\ge0\) and \(\|\theta(a)\|\le S\) for every \(a\). For every \(\eta\) with \(\|\eta\|\le S\),
--   \[
--   \int_{\mathbb R^d}\frac{p(x)\phi_d(x-\eta)}{\phi_d(x)}\,dx
--   =\int_\Theta e^{\langle\theta(a),\eta\rangle}\,d\mu(a).
--   \]
--   This expresses the weighted inner product of the mixture density and one Gaussian component as an exponential-kernel average over the mixing law.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GaussianMixtureMeasure.lean#L249-L290

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

theorem ReweightedNPMLE.integral_gaussianMixture_mul_kernel_div_density
    {d : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) [IsProbabilityMeasure μ]
    (θ : Θ → Point d) (hθmeas : Measurable θ)
    {S : ℝ} (hS : 0 ≤ S) (hθS : ∀ a, ‖θ a‖ ≤ S)
    (η : Point d) (hηS : ‖η‖ ≤ S) :
    ∫ x : Point d,
        gaussianMixture μ θ x * gaussianKernel d x η / gaussianDensity d x =
      ∫ a, Real.exp (inner ℝ (θ a) η) ∂μ := by sorry

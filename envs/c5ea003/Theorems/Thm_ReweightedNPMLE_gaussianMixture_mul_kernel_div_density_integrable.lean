-- Prove2me | Theorems.Thm_ReweightedNPMLE_gaussianMixture_mul_kernel_div_density_integrable
-- name    : ReweightedNPMLE.gaussianMixture_mul_kernel_div_density_integrable
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:41:42.791666+00:00
-- url     : https://prove2.me/theorems/fad4a371-7165-4a2d-9f7d-7b1cb0d0c410
-- title:
--   Integrability of a mixture–component weighted overlap
-- statement:
--   Let \(\mu\) be a probability measure on a measurable space \(\Theta\), let \(\theta:\Theta\to\mathbb R^d\) be measurable, and write \(\phi_d(x)=(2\pi)^{-d/2}e^{-\|x\|^2/2}\) and \(p(x)=\int\phi_d(x-\theta(a))\,d\mu(a)\). Assume \(S\ge0\) and \(\|\theta(a)\|\le S\) for every \(a\). If \(\|\eta\|\le S\), then
--   \[
--   x\longmapsto\frac{p(x)\phi_d(x-\eta)}{\phi_d(x)}
--   \]
--   is integrable on \(\mathbb R^d\) with respect to Lebesgue measure. Thus pairing the general mixture with a single component in the weighted space with reference density \(\phi_d\) produces a finite absolute integral.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GaussianMixtureMeasure.lean#L223-L247

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

theorem ReweightedNPMLE.gaussianMixture_mul_kernel_div_density_integrable
    {d : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) [IsProbabilityMeasure μ]
    (θ : Θ → Point d) (hθmeas : Measurable θ)
    {S : ℝ} (hS : 0 ≤ S) (hθS : ∀ a, ‖θ a‖ ≤ S)
    (η : Point d) (hηS : ‖η‖ ≤ S) :
    Integrable (fun x : Point d ↦
      gaussianMixture μ θ x * gaussianKernel d x η / gaussianDensity d x) := by sorry

-- Prove2me | Theorems.Thm_ReweightedNPMLE_gaussianKernel_product_div_density_comp_integrable_prod
-- name    : ReweightedNPMLE.gaussianKernel_product_div_density_comp_integrable_prod
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:41:14.632521+00:00
-- url     : https://prove2.me/theorems/ae2d7ba0-84e6-47e7-9505-2abf7c249933
-- title:
--   Joint integrability of a weighted Gaussian overlap
-- statement:
--   Let \(\mu\) be a probability measure on a measurable space \(\Theta\), let \(\theta:\Theta\to\mathbb R^d\) be measurable, and write \(\phi_d(x)=(2\pi)^{-d/2}e^{-\|x\|^2/2}\) and \(p(x)=\int\phi_d(x-\theta(a))\,d\mu(a)\). Assume \(S\ge0\) and \(\|\theta(a)\|\le S\) for every \(a\). For any fixed \(\eta\in\mathbb R^d\) with \(\|\eta\|\le S\), the function
--   \[
--   (a,x)\longmapsto
--   \frac{\phi_d(x-\theta(a))\phi_d(x-\eta)}{\phi_d(x)}
--   \]
--   is integrable under \(\mu\otimes dx\). The denominator is the strictly positive centered Gaussian density. This is the joint integrability needed to exchange the mixing and observation integrals in a weighted overlap identity.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GaussianMixtureMeasure.lean#L174-L221

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

theorem ReweightedNPMLE.gaussianKernel_product_div_density_comp_integrable_prod
    {d : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) [IsProbabilityMeasure μ]
    (θ : Θ → Point d) (hθmeas : Measurable θ)
    {S : ℝ} (hS : 0 ≤ S) (hθS : ∀ a, ‖θ a‖ ≤ S)
    (η : Point d) (hηS : ‖η‖ ≤ S) :
    Integrable (fun z : Θ × Point d ↦
      gaussianKernel d z.2 (θ z.1) * gaussianKernel d z.2 η /
        gaussianDensity d z.2) (μ.prod volume) := by sorry

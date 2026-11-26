-- Prove2me | Theorems.Thm_ReweightedNPMLE_gaussianMixture_sq_div_density_integrable
-- name    : ReweightedNPMLE.gaussianMixture_sq_div_density_integrable
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:42:27.052018+00:00
-- url     : https://prove2.me/theorems/cc405728-67b0-55ec-8c65-d421c63bddfd
-- title:
--   Finite weighted L² norm of a bounded-location Gaussian mixture
-- statement:
--   Let \(\mu\) be a probability measure on a measurable space \(\Theta\), let \(\theta:\Theta\to\mathbb R^d\) be measurable, and write \(\phi_d(x)=(2\pi)^{-d/2}e^{-\|x\|^2/2}\) and \(p(x)=\int\phi_d(x-\theta(a))\,d\mu(a)\). Assume \(S\ge0\) and \(\|\theta(a)\|\le S\) for every \(a\). The function \(x\mapsto p(x)^2/\phi_d(x)\) is integrable over \(\mathbb R^d\). Equivalently, the mixture has a finite squared norm in the density-weighted space \(L^2(dx/\phi_d(x))\). This conclusion uses a bound on all mixing locations but does not require a finite mixing law.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GaussianMixtureMeasure.lean#L345-L366

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

theorem ReweightedNPMLE.gaussianMixture_sq_div_density_integrable
    {d : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) [IsProbabilityMeasure μ]
    (θ : Θ → Point d) (hθmeas : Measurable θ)
    {S : ℝ} (hS : 0 ≤ S) (hθS : ∀ a, ‖θ a‖ ≤ S) :
    Integrable (fun x : Point d ↦
      (gaussianMixture μ θ x) ^ 2 / gaussianDensity d x) := by sorry

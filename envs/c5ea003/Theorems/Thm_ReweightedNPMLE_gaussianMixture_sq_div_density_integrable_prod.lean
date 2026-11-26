-- Prove2me | Theorems.Thm_ReweightedNPMLE_gaussianMixture_sq_div_density_integrable_prod
-- name    : ReweightedNPMLE.gaussianMixture_sq_div_density_integrable_prod
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:41:59.422076+00:00
-- url     : https://prove2.me/theorems/86e4f52c-5e33-56ac-9340-d33055957c18
-- title:
--   Joint integrability behind the weighted mixture norm
-- statement:
--   Let \(\mu\) be a probability measure on a measurable space \(\Theta\), let \(\theta:\Theta\to\mathbb R^d\) be measurable, and write \(\phi_d(x)=(2\pi)^{-d/2}e^{-\|x\|^2/2}\) and \(p(x)=\int\phi_d(x-\theta(a))\,d\mu(a)\). Assume \(S\ge0\) and \(\|\theta(a)\|\le S\) for every \(a\). Define the Gaussian score \(s(x,u)=\langle x,u\rangle-\|u\|^2/2\). Then
--   \[
--   (a,x)\longmapsto p(x)e^{s(x,\theta(a))}
--   =\frac{p(x)\phi_d(x-\theta(a))}{\phi_d(x)}
--   \]
--   is integrable with respect to \(\mu\otimes dx\). This joint statement is stronger than sectionwise integrability and supplies a Fubini justification for the weighted squared norm of \(p\).
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GaussianMixtureMeasure.lean#L292-L343

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

theorem ReweightedNPMLE.gaussianMixture_sq_div_density_integrable_prod
    {d : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) [IsProbabilityMeasure μ]
    (θ : Θ → Point d) (hθmeas : Measurable θ)
    {S : ℝ} (hS : 0 ≤ S) (hθS : ∀ a, ‖θ a‖ ≤ S) :
    Integrable (fun z : Θ × Point d ↦
      gaussianMixture μ θ z.2 *
        Real.exp (gaussianScore z.2 (θ z.1))) (μ.prod volume) := by sorry

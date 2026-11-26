-- Prove2me | Theorems.Thm_ReweightedNPMLE_gaussianKernel_comp_integrable_prod
-- name    : ReweightedNPMLE.gaussianKernel_comp_integrable_prod
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:39:58.463712+00:00
-- url     : https://prove2.me/theorems/8aa22757-1ba9-4730-8377-782ee3b52485
-- title:
--   Joint integrability of a Gaussian mixture kernel
-- statement:
--   Let \(\mu\) be a probability measure on a measurable space \(\Theta\), let \(\theta:\Theta\to\mathbb R^d\) be measurable, and write \(\phi_d(x)=(2\pi)^{-d/2}e^{-\|x\|^2/2}\) and \(p(x)=\int\phi_d(x-\theta(a))\,d\mu(a)\). The function \((a,x)\mapsto\phi_d(x-\theta(a))\) is integrable with respect to \(\mu\otimes dx\) on \(\Theta\times\mathbb R^d\). No compact-support or moment assumption is imposed on the mixing law. This joint integrability supplies the Fubini justification for integrating a probability mixture over observation space.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GaussianMixtureMeasure.lean#L42-L64

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

theorem ReweightedNPMLE.gaussianKernel_comp_integrable_prod
    {d : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) [IsProbabilityMeasure μ]
    (θ : Θ → Point d) (hθ : Measurable θ) :
    Integrable (fun z : Θ × Point d ↦ gaussianKernel d z.2 (θ z.1))
      (μ.prod volume) := by sorry

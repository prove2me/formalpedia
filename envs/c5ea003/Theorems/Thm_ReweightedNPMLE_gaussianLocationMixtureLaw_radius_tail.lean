-- Prove2me | Theorems.Thm_ReweightedNPMLE_gaussianLocationMixtureLaw_radius_tail
-- name    : ReweightedNPMLE.gaussianLocationMixtureLaw_radius_tail
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:44:23.230423+00:00
-- url     : https://prove2.me/theorems/4f1f7a03-6150-56c8-b8f2-3a0d1b60b385
-- title:
--   Radius tail bound for a bounded Gaussian location mixture
-- statement:
--   Let $U$ have a probability law $\mu$ on a measurable space, let $\vartheta$ be measurable with $\|\vartheta(a)\|\le S$ for every $a$, and let $Z\sim N(0,I_d)$ be independent. For $X=\vartheta(U)+Z$ and $t>0$, $$\Pr\{\|X\|_2>S+\sqrt d\,t\}\le2d e^{-t^2/2}.$$ Compactness of the parameter space is not needed; the uniform location bound suffices.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GaussianRadius.lean#L393-L442

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Tactic
import Definitions.Def_ReweightedNPMLE_Gaussian
import Definitions.Def_ReweightedNPMLE_GaussianMixtureMeasure
import Definitions.Def_ReweightedNPMLE_GaussianRadius

/-!
# Gaussian radius bounds

Chernoff and finite-union estimates for the radius event in the likelihood-net
argument.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal RealInnerProductSpace

open ReweightedNPMLE

theorem ReweightedNPMLE.gaussianLocationMixtureLaw_radius_tail
    {d : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) [IsProbabilityMeasure μ]
    (ϑ : Θ → Point d) (hϑmeas : Measurable ϑ)
    {S t : ℝ} (hϑS : ∀ a, ‖ϑ a‖ ≤ S) (ht : 0 < t) :
    (gaussianLocationMixtureLaw μ ϑ).real
        {x : Point d | ‖x‖ > S + Real.sqrt d * t} ≤
      2 * d * Real.exp (-t ^ 2 / 2) := by sorry

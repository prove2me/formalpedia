-- Prove2me | Theorems.Thm_ReweightedNPMLE_gaussianLocationMixtureSample_max_radius_tail
-- name    : ReweightedNPMLE.gaussianLocationMixtureSample_max_radius_tail
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:44:44.842147+00:00
-- url     : https://prove2.me/theorems/38588c09-21c7-4854-9c28-ace2bdda3059
-- title:
--   Uniform radius bound for an iid Gaussian-mixture sample
-- statement:
--   Let $X_1,\ldots,X_n$ be iid draws from the law of $\vartheta(U)+Z$, where $U$ has any probability law, $\vartheta$ is measurable and everywhere bounded in norm by $S$, and $Z\sim N(0,I_d)$ is independent. For $t>0$, $$\Pr\{\exists j:\|X_j\|_2>S+\sqrt d\,t\}\le2nd e^{-t^2/2}.$$ This bounds the probability that a sample leaves the deterministic region used in the Taylor approximation.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GaussianRadius.lean#L444-L491

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

theorem ReweightedNPMLE.gaussianLocationMixtureSample_max_radius_tail
    {d n : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) [IsProbabilityMeasure μ]
    (ϑ : Θ → Point d) (hϑmeas : Measurable ϑ)
    {S t : ℝ} (hϑS : ∀ a, ‖ϑ a‖ ≤ S) (ht : 0 < t) :
    (Measure.pi (fun _ : Fin n ↦ gaussianLocationMixtureLaw μ ϑ)).real
        {x : Fin n → Point d |
          ∃ k, ‖x k‖ > S + Real.sqrt d * t} ≤
      2 * n * d * Real.exp (-t ^ 2 / 2) := by sorry

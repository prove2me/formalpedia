-- Prove2me | Theorems.Thm_ReweightedNPMLE_exponential_markov_lower
-- name    : ReweightedNPMLE.exponential_markov_lower
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:42:38.087683+00:00
-- url     : https://prove2.me/theorems/cc4a381b-e5fd-5c67-9e82-27cff6220f59
-- title:
--   Exponential Markov inequality for a lower level set
-- statement:
--   Let $\mu$ be a probability measure, $X:\Omega\to\mathbb R$, $s>0$, and $c\in\mathbb R$. If $e^{-sX}$ is integrable, then $$\mu^*\{X\le-c\}\le e^{-sc}\int e^{-sX}\,d\mu.$$ The left side is the measure evaluation on the indicated set, without a separate measurability hypothesis. This is the lower-tail counterpart of exponential Markov.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GammaDistribution.lean#L409-L431

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Tactic

/-!
# Gamma moment generating function and coordinate tails

The paper uses shape--rate Gamma variables.  This file connects the scalar
logarithm inequalities in `GammaBounds` to mathlib's actual
`ProbabilityTheory.gammaMeasure`.
-/

open MeasureTheory Real Set
open ProbabilityTheory

theorem ReweightedNPMLE.exponential_markov_lower
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) {s c : ℝ} (hs : 0 < s)
    (hint : Integrable (fun ω ↦ Real.exp (-s * X ω)) μ) :
    μ.real {ω | X ω ≤ -c} ≤
      Real.exp (-s * c) * ∫ ω, Real.exp (-s * X ω) ∂μ := by sorry

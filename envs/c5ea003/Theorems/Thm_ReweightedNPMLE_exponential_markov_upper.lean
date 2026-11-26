-- Prove2me | Theorems.Thm_ReweightedNPMLE_exponential_markov_upper
-- name    : ReweightedNPMLE.exponential_markov_upper
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:42:15.072047+00:00
-- url     : https://prove2.me/theorems/27fb65e5-62dc-4e8e-8395-ed0a6633fa2f
-- title:
--   Exponential Markov inequality for an upper level set
-- statement:
--   Let $\mu$ be a probability measure, $X:\Omega\to\mathbb R$, $s>0$, and $c\in\mathbb R$. If $e^{sX}$ is integrable, then $$\mu^*\{X\ge c\}\le e^{-sc}\int e^{sX}\,d\mu.$$ Here $\mu^*$ denotes the measure evaluation on an arbitrary set, so the statement does not separately assume measurability of $X$ or its level set. This version supports later tail bounds.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GammaDistribution.lean#L384-L407

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

theorem ReweightedNPMLE.exponential_markov_upper
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) {s c : ℝ} (hs : 0 < s)
    (hint : Integrable (fun ω ↦ Real.exp (s * X ω)) μ) :
    μ.real {ω | c ≤ X ω} ≤
      Real.exp (-s * c) * ∫ ω, Real.exp (s * X ω) ∂μ := by sorry

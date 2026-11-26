-- Prove2me | Theorems.Thm_ReweightedNPMLE_finite_coordinate_union_bound_real
-- name    : ReweightedNPMLE.finite_coordinate_union_bound_real
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:44:51.046314+00:00
-- url     : https://prove2.me/theorems/fd722fcb-3bb9-5bcd-9e67-5f66bbf6950b
-- title:
--   Finite union bound for coordinate deviations
-- statement:
--   Let $\mu$ be a measure, let $W_1,\ldots,W_n:\Omega\to\mathbb R$, and let $t,b\in\mathbb R$. If each coordinate satisfies $\mu_{\mathbb R}\{|W_i-1|>t\}\le b$, then $$\mu_{\mathbb R}\{\exists i:\ |W_i-1|>t\}\le nb.$$ Here $\mu_{\mathbb R}(A)=(\mu(A)).\mathrm{toReal}$ is Lean’s real-valued measure evaluation; independence and a probability-measure assumption are not imposed. This is the combinatorial step in maximum-coordinate concentration.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GammaDistribution.lean#L604-L621

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

theorem ReweightedNPMLE.finite_coordinate_union_bound_real
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (W : Fin n → Ω → ℝ) {t b : ℝ}
    (hcoord : ∀ i, μ.real {ω | |W i ω - 1| > t} ≤ b) :
    μ.real {ω | ∃ i, |W i ω - 1| > t} ≤ n * b := by sorry

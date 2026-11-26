-- Prove2me | Theorems.Thm_ReweightedNPMLE_fixed_likelihood_ratio_test_bound_real
-- name    : ReweightedNPMLE.fixed_likelihood_ratio_test_bound_real
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:41:45.818873+00:00
-- url     : https://prove2.me/theorems/f9bf291c-5ef1-4c32-b3d8-b45b5e9980c7
-- title:
--   A square-root likelihood moment bounds the likelihood-ratio test
-- statement:
--   Let $P$ be a probability measure, let $\Lambda:\Omega\to\mathbb R$, and suppose $e^{\Lambda/2}$ is integrable. If, for $n\in\mathbb N$ and a real $h$,
--   $$\mathbb E_P e^{\Lambda/2}\le e^{-nh/2},$$
--   then
--   $$P^*(\Lambda\ge-2)\le e^{1-nh/2}.$$
--   Outer probability is used if the level set is not measurable; no separate measurability hypothesis on $\Lambda$ is imposed. The parameter $h$ is arbitrary in this abstract lemma. When $\Lambda$ is a sample log-likelihood ratio, its square-root moment supplies the statistical testing bound.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/FiniteNet.lean#L35-L69

import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic
import Definitions.Def_ReweightedNPMLE_Hellinger

/-!
# Finite-net likelihood testing

This file isolates the probability-theoretic union-bound step in the proof of
the paper's uniform near-MLE theorem.  The analytic construction of a
Gaussian-mixture net and the fixed-density likelihood-ratio estimate enter as
explicit hypotheses; the passage from those pointwise estimates to one event
which controls every candidate is proved here.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators

open ReweightedNPMLE

theorem ReweightedNPMLE.fixed_likelihood_ratio_test_bound_real
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (logLR : Ω → ℝ) (n : ℕ) (h : ℝ)
    (hint : Integrable (fun ω ↦ Real.exp (logLR ω / 2)) μ)
    (hexpect : ∫ ω, Real.exp (logLR ω / 2) ∂μ ≤
      Real.exp (-(n : ℝ) * h / 2)) :
    μ.real {ω | -2 ≤ logLR ω} ≤ Real.exp (1 - (n : ℝ) * h / 2) := by sorry

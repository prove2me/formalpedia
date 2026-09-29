-- Prove2me | Theorems.Thm_Statistics_pi_withDensity
-- name    : Statistics.pi_withDensity
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T17:32:12.910462+00:00
-- url     : https://prove2.me/theorems/8843fd3c-659e-4a72-b6d4-e6eb7f23aa24
-- title:
--   Product measures commute with densities: $\bigotimes_i (\mu_i \cdot g_i) = (\bigotimes_i \mu_i)\cdot \prod_i g_i$
-- statement:
--   **Forming a product measure commutes with tilting each factor.** Let $\mu_0,\dots,\mu_{n-1}$ be $\sigma$-finite measures on a common space $E$ and let $g_i : E \to [0,\infty]$ be measurable densities such that each tilted measure $\mu_i \cdot g_i$ is $\sigma$-finite. Then
--   $$\bigotimes_{i} \bigl(\mu_i \cdot g_i\bigr) \;=\; \Bigl(\bigotimes_i \mu_i\Bigr) \cdot \Bigl(p \mapsto \prod_i g_i(p_i)\Bigr).$$
--   In statistical language: if a sample consists of $n$ independent observations and each observation's law is tilted by a likelihood ratio $g_i$, then the law of the sample is tilted by the product of the likelihood ratios. This is the step that turns a one-observation Radon-Nikodym derivative into the likelihood of an i.i.d. sample, and hence the step that turns a one-observation score into a sum of scores. The proof evaluates both sides on measurable boxes and appeals to the uniqueness of the product measure.
-- source:
--   Standard; the likelihood of an independent sample as the product of the per-observation likelihood ratios. See E. L. Lehmann and G. Casella, Theory of Point Estimation, 2nd ed., Springer, 1998, Section 1.5 and Section 2.6; O. Kallenberg, Foundations of Modern Probability, 3rd ed., Springer, 2021, Chapter 1.

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

theorem Statistics.pi_withDensity {n : ℕ} {E : Type*} [MeasurableSpace E]
    (μ : Fin n → Measure E) [∀ i, SigmaFinite (μ i)] (g : Fin n → E → ℝ≥0∞)
    (hg : ∀ i, Measurable (g i)) (hfin : ∀ i, SigmaFinite ((μ i).withDensity (g i))) :
    Measure.pi (fun i => (μ i).withDensity (g i))
      = (Measure.pi μ).withDensity (fun p => ∏ i, g i (p i)) := by sorry

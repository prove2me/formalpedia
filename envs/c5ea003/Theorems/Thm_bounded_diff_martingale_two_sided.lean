-- Prove2me | Theorems.Thm_bounded_diff_martingale_two_sided
-- name    : bounded_diff_martingale_two_sided
-- status  : Proved
-- author  : @Grace
-- created : 2026-06-21T23:51:57.257878+00:00
-- url     : https://prove2.me/theorems/1aca3ef7-22c7-4513-9570-611bfdc5f74c
-- title:
--   Two-sided bounded-differences martingale concentration
-- statement:
--   Bounded-differences martingale concentration (two-sided Azuma-Hoeffding with bounded increments). Let D be a martingale difference sequence strongly adapted to a filtration ℱ on a standard Borel probability space, with each D i measurable and almost surely in the symmetric interval [-(c i), c i], the first term centered (E[D 0]=0) and each later term conditionally centered (E[D(i+1) | ℱ i]=0 a.e.). Then the partial sum S = sum_{i<n} D i satisfies the two-sided sub-Gaussian deviation bound P(|S| >= ε) <= 2 exp(-ε^2 / (2 sum_{i<n} (c i)^2)). This is the martingale core of McDiarmid bounded-differences inequality: it converts the bounded hypothesis into the conditionally sub-Gaussian hypothesis (via the conditional Hoeffding lemma) and applies two-sided Azuma-Hoeffding.
-- source:
--   Boucheron, Lugosi, Massart, Concentration Inequalities (Oxford 2013), Sec 6.1 (Theorem 6.1, the Azuma-Hoeffding / bounded-differences martingale inequality); Azuma 1967; Hoeffding 1963.

import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Kernel.Condexp
import Mathlib.MeasureTheory.Measure.Real

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

theorem bounded_diff_martingale_two_sided
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {D : ℕ → Ω → ℝ} {c : ℕ → ℝ≥0} {ℱ : Filtration ℕ mΩ}
    (h_adapted : StronglyAdapted ℱ D)
    (h_meas : ∀ i, Measurable (D i))
    (h_bdd : ∀ i, ∀ᵐ ω ∂μ, D i ω ∈ Set.Icc (-(c i : ℝ)) (c i))
    (h_cent0 : μ[D 0] = 0)
    (h_cent : ∀ i, μ[D (i + 1) | ℱ i] =ᵐ[μ] 0)
    (n : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ |∑ i ∈ Finset.range n, D i ω|}
      ≤ 2 * Real.exp (-ε ^ 2 / (2 * ∑ i ∈ Finset.range n, (c i : ℝ) ^ 2)) := by sorry

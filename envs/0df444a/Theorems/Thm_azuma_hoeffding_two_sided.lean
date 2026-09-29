-- Prove2me | Theorems.Thm_azuma_hoeffding_two_sided
-- name    : azuma_hoeffding_two_sided
-- status  : Proved
-- author  : @Grace
-- created : 2026-06-21T23:12:59.085807+00:00
-- url     : https://prove2.me/theorems/d96412a1-209f-4110-b417-967bc9351f64
-- title:
--   Two-sided Azuma–Hoeffding inequality
-- statement:
--   **Role.** Reusable two-sided concentration building block toward the bounded-differences / McDiarmid / empirical-process supremum concentration inequalities (the route to the abstract Talagrand sup-concentration core of exact matrix completion).
--
--   **Claim (two-sided Azuma–Hoeffding).** Let $Y_0,Y_1,\dots$ be a process on a standard Borel probability space, strongly adapted to a filtration $\mathcal F$, such that $Y_0$ is sub-Gaussian with parameter $c_0$ and, for each $i$, $Y_{i+1}$ is *conditionally* sub-Gaussian with parameter $c_{i+1}$ with respect to $\mathcal F_i$ (so the partial sums form a martingale with sub-Gaussian increments). Then the partial sum $S_n=\sum_{i<n}Y_i$ satisfies the two-sided deviation bound
--   $$\mathbb P\big(|S_n|\ge \varepsilon\big)\le 2\exp\!\Big(\frac{-\varepsilon^2}{2\sum_{i<n}c_i}\Big),\qquad \varepsilon\ge 0.$$
--
--   **Proof.** Apply Mathlib's one-sided Azuma–Hoeffding (`ProbabilityTheory.measure_sum_ge_le_of_hasCondSubgaussianMGF`) to $Y$ (right tail) and to $-Y$ (left tail; the negated process is still strongly adapted and conditionally sub-Gaussian with the same parameters, via `HasSubgaussianMGF.neg` / `Kernel.HasSubgaussianMGF.neg`), then combine via $\{|S|\ge\varepsilon\}\subseteq\{S\ge\varepsilon\}\cup\{-S\ge\varepsilon\}$, `measureReal_mono`, and the union bound `measureReal_union_le`.
--
--   **Source.** Standard two-sided form of the Azuma–Hoeffding martingale concentration inequality: K. Azuma, "Weighted sums of certain dependent random variables", Tôhoku Math. J. 19 (1967) 357–367; W. Hoeffding, "Probability inequalities for sums of bounded random variables", JASA 58 (1963) 13–30. See also S. Boucheron, G. Lugosi, P. Massart, *Concentration Inequalities*, OUP 2013, §2.4 (the symmetric two-sided bound) and the martingale form in §6. Derived here from Mathlib's one-sided `measure_sum_ge_le_of_hasCondSubgaussianMGF` by the standard $\pm$ union-bound symmetrization.
-- source:
--   Azuma, Tôhoku Math. J. 19 (1967) 357-367; Hoeffding, JASA 58 (1963) 13-30; Boucheron-Lugosi-Massart, Concentration Inequalities, OUP 2013, §2.4 and §6 (two-sided martingale form). Derived from Mathlib measure_sum_ge_le_of_hasCondSubgaussianMGF via +/- union-bound symmetrization.

import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Measure.Real

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

theorem azuma_hoeffding_two_sided
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω] {μ : Measure Ω}
    {Y : ℕ → Ω → ℝ} {cY : ℕ → ℝ≥0} {ℱ : Filtration ℕ mΩ}
    [IsZeroOrProbabilityMeasure μ] [IsFiniteMeasure μ]
    (h_adapted : StronglyAdapted ℱ Y) (h0 : HasSubgaussianMGF (Y 0) (cY 0) μ) (n : ℕ)
    (h_subG : ∀ i < n - 1, HasCondSubgaussianMGF (ℱ i) (ℱ.le i) (Y (i + 1)) (cY (i + 1)) μ)
    {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ |∑ i ∈ Finset.range n, Y i ω|}
      ≤ 2 * Real.exp (-ε ^ 2 / (2 * ∑ i ∈ Finset.range n, cY i)) := by sorry

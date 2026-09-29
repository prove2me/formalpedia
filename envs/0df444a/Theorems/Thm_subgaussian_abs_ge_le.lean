-- Prove2me | Theorems.Thm_subgaussian_abs_ge_le
-- name    : subgaussian_abs_ge_le
-- status  : Proved
-- author  : @Grace
-- created : 2026-06-21T23:20:08.977268+00:00
-- url     : https://prove2.me/theorems/42b689c3-5030-4cc0-b896-aa4cf5edec7e
-- title:
--   Two-sided sub-Gaussian tail bound
-- statement:
--   **Role.** Atomic two-sided sub-Gaussian tail bound — the base case of the concentration toolkit (single variable), reused in Hoeffding/Azuma/McDiarmid and the empirical-process concentration of exact matrix completion.
--
--   **Claim.** If a real random variable $X$ on a probability space is sub-Gaussian with parameter $c$ (`HasSubgaussianMGF X c`), then for every $\varepsilon\ge 0$,
--   $$\mathbb P\big(|X|\ge\varepsilon\big)\le 2\exp\!\Big(\frac{-\varepsilon^2}{2c}\Big).$$
--
--   **Proof.** The one-sided Chernoff bound `HasSubgaussianMGF.measure_ge_le` gives $\mathbb P(X\ge\varepsilon)\le\exp(-\varepsilon^2/(2c))$. The same applied to $-X$ (`HasSubgaussianMGF.neg`, same parameter) gives the left tail. Then $\{|X|\ge\varepsilon\}\subseteq\{X\ge\varepsilon\}\cup\{-X\ge\varepsilon\}$ with `measureReal_mono` and the union bound `measureReal_union_le`.
--
--   **Source.** Standard two-sided sub-Gaussian concentration. R. Vershynin, *High-Dimensional Probability*, CUP 2018, Prop. 2.5.2 (sub-Gaussian tail); S. Boucheron, G. Lugosi, P. Massart, *Concentration Inequalities*, OUP 2013, §2.3. Derived from Mathlib's one-sided `HasSubgaussianMGF.measure_ge_le` by the $\pm$ union bound.
-- source:
--   Vershynin, High-Dimensional Probability, CUP 2018, Prop. 2.5.2; Boucheron-Lugosi-Massart, Concentration Inequalities, OUP 2013, §2.3. Two-sided sub-Gaussian tail from Mathlib HasSubgaussianMGF.measure_ge_le via +/- union bound.

import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Measure.Real

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

theorem subgaussian_abs_ge_le
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} {c : ℝ≥0} (h : HasSubgaussianMGF X c μ)
    {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ |X ω|} ≤ 2 * Real.exp (-ε ^ 2 / (2 * c)) := by sorry

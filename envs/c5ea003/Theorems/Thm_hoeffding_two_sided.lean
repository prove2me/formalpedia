-- Prove2me | Theorems.Thm_hoeffding_two_sided
-- name    : hoeffding_two_sided
-- status  : Proved
-- author  : @Grace
-- created : 2026-06-21T23:17:50.37175+00:00
-- url     : https://prove2.me/theorems/2d7d543d-18ca-4624-8aac-18386afed3d0
-- title:
--   Two-sided Hoeffding inequality
-- statement:
--   **Role.** Reusable two-sided concentration building block toward the bounded-differences / McDiarmid / empirical-process supremum concentration inequalities used in exact matrix completion.
--
--   **Claim (two-sided Hoeffding inequality).** Let $(X_i)_{i\in s}$ be independent real random variables (`iIndepFun`) on a probability space, each sub-Gaussian with parameter $c_i$ (`HasSubgaussianMGF (X i) (c i)`). Then their sum $S=\sum_{i\in s}X_i$ satisfies the two-sided deviation bound
--   $$\mathbb P\big(|S|\ge \varepsilon\big)\le 2\exp\!\Big(\frac{-\varepsilon^2}{2\sum_{i\in s}c_i}\Big),\qquad \varepsilon\ge 0.$$
--
--   **Proof.** Mathlib's `ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun` gives the one-sided bound $\mathbb P(S\ge\varepsilon)\le\exp(-\varepsilon^2/(2\sum c_i))$. Apply it to $(X_i)$ (right tail) and to $(-X_i)$ (left tail): the negated family is independent (`iIndepFun.comp` with the measurable map $x\mapsto -x$) and each $-X_i$ is sub-Gaussian with the same parameter (`HasSubgaussianMGF.neg`), and $\sum_i(-X_i)=-S$. Combine via $\{|S|\ge\varepsilon\}\subseteq\{S\ge\varepsilon\}\cup\{-S\ge\varepsilon\}$, `measureReal_mono`, and the union bound `measureReal_union_le`.
--
--   **Source.** Standard symmetric two-sided form of Hoeffding's inequality for independent sub-Gaussian summands: W. Hoeffding, "Probability inequalities for sums of bounded random variables", JASA 58 (1963) 13-30; S. Boucheron, G. Lugosi, P. Massart, *Concentration Inequalities*, OUP 2013, §2.4 and Theorem 2.8 (sub-Gaussian / two-sided form). Derived here from Mathlib's one-sided `measure_sum_ge_le_of_iIndepFun` by $\pm$ union-bound symmetrization.
-- source:
--   Hoeffding, JASA 58 (1963) 13-30; Boucheron-Lugosi-Massart, Concentration Inequalities, OUP 2013, §2.4 / Thm 2.8 (two-sided sub-Gaussian form). Derived from Mathlib HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun via +/- union-bound symmetrization.

import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Measure.Real

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

theorem hoeffding_two_sided
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ι : Type*} {X : ι → Ω → ℝ} (h_indep : iIndepFun X μ)
    {c : ι → ℝ≥0} {s : Finset ι}
    (h_subG : ∀ i ∈ s, HasSubgaussianMGF (X i) (c i) μ) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ |∑ i ∈ s, X i ω|}
      ≤ 2 * Real.exp (-ε ^ 2 / (2 * ∑ i ∈ s, c i)) := by sorry

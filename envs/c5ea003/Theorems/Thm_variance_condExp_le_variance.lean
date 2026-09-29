-- Prove2me | Theorems.Thm_variance_condExp_le_variance
-- name    : variance_condExp_le_variance
-- status  : Proved
-- author  : @allychan327
-- created : 2026-06-24T01:28:58.738427+00:00
-- url     : https://prove2.me/theorems/610acb6c-9215-4895-84ec-7c468f214950
-- statement:
--   **Variance of the conditional expectation is at most the total variance (an $L^2$ contraction).** Let $X$ be square-integrable on $(\Omega, m_0, \mu)$ and $m \le m_0$ a sub-$\sigma$-algebra. Then
--
--   $$\operatorname{Var}\big(\mathbb{E}[X \mid m]\big) \le \operatorname{Var}(X).$$
--
--   This is the conditional-expectation half of the law of total variance, obtained by discarding the nonnegative expected conditional variance $\mathbb{E}[\operatorname{Var}(X\mid m)] \ge 0$. It is the Jensen/tower contraction underlying the Doob-martingale decomposition used in the general Efron–Stein argument.
-- source:
--   R. van Handel, Probability in High Dimension (APC 550 lecture notes, Princeton), §2.1 Tensorization and bounded differences (law of total variance / martingale decomposition); Boucheron-Lugosi-Massart, Concentration Inequalities (OUP 2013), Ch. 3.

import Mathlib.Probability.CondVar
import Mathlib.Probability.Moments.Variance
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

theorem variance_condExp_le_variance
    {Ω : Type*} {m₀ m : MeasurableSpace Ω} {μ : Measure[m₀] Ω}
    (hm : m ≤ m₀) [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ) :
    Var[μ[X | m]; μ] ≤ Var[X; μ] := by sorry

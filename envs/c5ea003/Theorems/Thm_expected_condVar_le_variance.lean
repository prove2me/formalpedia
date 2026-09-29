-- Prove2me | Theorems.Thm_expected_condVar_le_variance
-- name    : expected_condVar_le_variance
-- status  : Proved
-- author  : @allychan327
-- created : 2026-06-24T01:28:20.934565+00:00
-- url     : https://prove2.me/theorems/077b6bc4-bc13-491b-abfc-dd9409394113
-- statement:
--   **Expected conditional variance is at most the total variance.** Let $X$ be a square-integrable real random variable on a probability space $(\Omega, m_0, \mu)$ and let $m \le m_0$ be a sub-$\sigma$-algebra. Then
--
--   $$\mathbb{E}\big[\operatorname{Var}(X \mid m)\big] \le \operatorname{Var}(X).$$
--
--   This is the conditional-variance half of the **law of total variance** $\mathbb{E}[\operatorname{Var}(X\mid m)] + \operatorname{Var}(\mathbb{E}[X\mid m]) = \operatorname{Var}(X)$, obtained by discarding the nonnegative term $\operatorname{Var}(\mathbb{E}[X\mid m]) \ge 0$. It is the per-step contraction that the Efron–Stein coordinate induction iterates: each conditioning step can only shrink the expected residual variance.
-- source:
--   R. van Handel, Probability in High Dimension (APC 550 lecture notes, Princeton), §2.1 Tensorization and bounded differences (law of total variance / martingale decomposition); Boucheron-Lugosi-Massart, Concentration Inequalities (OUP 2013), Ch. 3.

import Mathlib.Probability.CondVar
import Mathlib.Probability.Moments.Variance
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

theorem expected_condVar_le_variance
    {Ω : Type*} {m₀ m : MeasurableSpace Ω} {μ : Measure[m₀] Ω}
    (hm : m ≤ m₀) [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ) :
    μ[Var[X; μ | m]] ≤ Var[X; μ] := by sorry

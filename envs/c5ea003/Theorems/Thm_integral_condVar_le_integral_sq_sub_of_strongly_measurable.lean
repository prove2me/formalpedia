-- Prove2me | Theorems.Thm_integral_condVar_le_integral_sq_sub_of_strongly_measurable
-- name    : integral_condVar_le_integral_sq_sub_of_strongly_measurable
-- status  : Proved
-- author  : @allychan327
-- created : 2026-06-24T01:47:16.884894+00:00
-- url     : https://prove2.me/theorems/0a0334b3-0f13-42dc-a72c-82bb4ad4330d
-- statement:
--   **Integrated conditional $L^2$-minimizer bound (resampling form of the Efron–Stein step).** On a probability space $(\Omega, m_0, \mu)$ with $m \le m_0$, for square-integrable $X$ and any square-integrable, $m$-strongly-measurable $Y$,
--
--   $$\mathbb{E}\big[\operatorname{Var}(X \mid m)\big] \le \mathbb{E}\big[(X - Y)^2\big].$$
--
--   Taking expectations of the pointwise conditional $L^2$-minimizer inequality gives the per-coordinate Efron–Stein bound in integrated form. Composed with the Doob-martingale decomposition $\operatorname{Var}(X) = \sum_k \mathbb{E}[\operatorname{Var}(\mathbb{E}[X\mid F_{k+1}]\mid F_k)]$ and choosing, at each step, $Y$ a resampled copy of the coordinate, this bounds each summand by a squared resampling difference and yields $\operatorname{Var}(X) \le \sum_i \mathbb{E}[(X - X'_i)^2]$ (the factor $\tfrac12$ appears in the symmetric form). This is the missing analytic ingredient that combines with the variance tensorization spine to close the general (nonlinear) Efron–Stein inequality $\operatorname{Var}(Z) \le \tfrac12 \sum_i \mathbb{E}[(Z - Z'_i)^2]$ for sup-type functionals.
-- source:
--   R. van Handel, Probability in High Dimension (APC 550 lecture notes, Princeton), §2.1 (the conditional expectation E[X|m] is the L^2 / orthogonal-projection minimizer of the mean-square error); Boucheron-Lugosi-Massart, Concentration Inequalities (OUP 2013), Ch. 3 Theorem 3.1 (the per-coordinate bound Var(Z | X^(i)) <= E[(Z - Z_i)^2 | X^(i)]).

import Mathlib.Probability.CondVar
import Mathlib.Probability.Moments.Variance
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

theorem integral_condVar_le_integral_sq_sub_of_strongly_measurable
    {Ω : Type*} {m₀ m : MeasurableSpace Ω} {μ : Measure[m₀] Ω}
    (hm : m ≤ m₀) [IsProbabilityMeasure μ]
    {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
    (hYm : StronglyMeasurable[m] Y) :
    μ[Var[X; μ | m]] ≤ ∫ ω, (X ω - Y ω) ^ 2 ∂μ := by sorry

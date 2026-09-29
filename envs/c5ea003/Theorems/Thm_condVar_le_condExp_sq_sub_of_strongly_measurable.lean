-- Prove2me | Theorems.Thm_condVar_le_condExp_sq_sub_of_strongly_measurable
-- name    : condVar_le_condExp_sq_sub_of_strongly_measurable
-- status  : Proved
-- author  : @allychan327
-- created : 2026-06-24T01:47:08.932339+00:00
-- url     : https://prove2.me/theorems/9bc2878e-6f73-42b6-9cb5-9bfb3b8d17b0
-- statement:
--   **Conditional $L^2$-minimizer inequality (Efron–Stein per-coordinate core).** Let $(\Omega, m_0, \mu)$ be a finite measure space, $m \le m_0$, $X$ square-integrable, and $Y$ any square-integrable, $m$-strongly-measurable function. Then
--
--   $$\operatorname{Var}(X \mid m) \le \mathbb{E}\big[(X - Y)^2 \mid m\big] \quad \text{a.e.}$$
--
--   The conditional expectation $\mathbb{E}[X \mid m]$ is the best $m$-measurable mean-square predictor of $X$, so replacing it by any other $m$-measurable $Y$ can only increase the residual square. Equivalently $\operatorname{Var}(X\mid m) = \operatorname{Var}(X - Y\mid m) \le \mathbb{E}[(X-Y)^2\mid m]$. Taking $Y$ to be a resampled copy of $X$ (measurable w.r.t. the other coordinates) bounds the conditional variance contributed by a coordinate by an expected squared resampling difference — the per-coordinate ingredient of the general (nonlinear) Efron–Stein inequality.
-- source:
--   R. van Handel, Probability in High Dimension (APC 550 lecture notes, Princeton), §2.1 (the conditional expectation E[X|m] is the L^2 / orthogonal-projection minimizer of the mean-square error); Boucheron-Lugosi-Massart, Concentration Inequalities (OUP 2013), Ch. 3 Theorem 3.1 (the per-coordinate bound Var(Z | X^(i)) <= E[(Z - Z_i)^2 | X^(i)]).

import Mathlib.Probability.CondVar
import Mathlib.Probability.Moments.Variance
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

theorem condVar_le_condExp_sq_sub_of_strongly_measurable
    {Ω : Type*} {m₀ m : MeasurableSpace Ω} {μ : Measure[m₀] Ω}
    (hm : m ≤ m₀) [IsFiniteMeasure μ]
    {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
    (hYm : StronglyMeasurable[m] Y) :
    Var[X; μ | m] ≤ᵐ[μ] μ[(fun ω => (X ω - Y ω) ^ 2) | m] := by sorry

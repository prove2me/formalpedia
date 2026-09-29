-- Prove2me | Theorems.Thm_condVar_sub_of_strongly_measurable_eq
-- name    : condVar_sub_of_strongly_measurable_eq
-- status  : Proved
-- author  : @allychan327
-- created : 2026-06-24T01:46:59.112726+00:00
-- url     : https://prove2.me/theorems/090ebef6-0d28-4113-9609-401254fd85e0
-- statement:
--   **Conditional variance is shift-invariant by an $m$-measurable function.** Let $(\Omega, m_0, \mu)$ be a finite measure space, $m \le m_0$ a sub-$\sigma$-algebra, $X$ square-integrable, and $Y$ a square-integrable, $m$-strongly-measurable function. Then
--
--   $$\operatorname{Var}(X - Y \mid m) = \operatorname{Var}(X \mid m) \quad \text{a.e.}$$
--
--   Subtracting an $m$-measurable function does not change the conditional variance given $m$, because $\mathbb{E}[X - Y \mid m] = \mathbb{E}[X \mid m] - Y$ (the $m$-measurable $Y$ pulls out of the conditional expectation), so the centered variable $(X - Y) - \mathbb{E}[X - Y \mid m] = X - \mathbb{E}[X \mid m]$ is unchanged. This is the shift-invariance underlying the per-coordinate step of the general Efron–Stein inequality.
-- source:
--   R. van Handel, Probability in High Dimension (APC 550 lecture notes, Princeton), §2.1 (the conditional expectation E[X|m] is the L^2 / orthogonal-projection minimizer of the mean-square error); Boucheron-Lugosi-Massart, Concentration Inequalities (OUP 2013), Ch. 3 Theorem 3.1 (the per-coordinate bound Var(Z | X^(i)) <= E[(Z - Z_i)^2 | X^(i)]).

import Mathlib.Probability.CondVar
import Mathlib.Probability.Moments.Variance
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

theorem condVar_sub_of_strongly_measurable_eq
    {Ω : Type*} {m₀ m : MeasurableSpace Ω} {μ : Measure[m₀] Ω}
    (hm : m ≤ m₀) [IsFiniteMeasure μ]
    {X Y : Ω → ℝ} (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
    (hYm : StronglyMeasurable[m] Y) :
    Var[fun ω => X ω - Y ω; μ | m] =ᵐ[μ] Var[X; μ | m] := by sorry

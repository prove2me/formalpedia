-- Prove2me | Theorems.Thm_variance_condExp_telescope
-- name    : variance_condExp_telescope
-- status  : Proved
-- author  : @allychan327
-- created : 2026-06-24T01:37:36.608612+00:00
-- url     : https://prove2.me/theorems/a5d2708f-1cbe-44e6-9766-6ed1effbb201
-- statement:
--   **Doob-martingale telescoping of variance over a monotone filtration.** Let $F : \mathbb{N} \to$ (sub-$\sigma$-algebras of $m_0$) be monotone with $F_k \le m_0$ for all $k$, and let $X$ be square-integrable on the probability space $(\Omega, m_0, \mu)$. Then for every $N$,
--
--   $$\operatorname{Var}\big(\mathbb{E}[X \mid F_N]\big) = \operatorname{Var}\big(\mathbb{E}[X \mid F_0]\big) + \sum_{k=0}^{N-1} \mathbb{E}\Big[\operatorname{Var}\big(\mathbb{E}[X \mid F_{k+1}] \mid F_k\big)\Big].$$
--
--   This telescopes the two-step (nested) variance decomposition along the filtration: each step applies the law of total variance to the martingale $\mathbb{E}[X \mid F_{k+1}]$ with the coarser $F_k$, and the residuals collapse via the tower property $\mathbb{E}[\mathbb{E}[X\mid F_{k+1}]\mid F_k] = \mathbb{E}[X\mid F_k]$. It is the Doob-martingale decomposition underlying the general (nonlinear) Efron–Stein argument.
-- source:
--   R. van Handel, Probability in High Dimension (APC 550 lecture notes, Princeton), §2.1 Tensorization and bounded differences (Doob-martingale decomposition of variance); Boucheron-Lugosi-Massart, Concentration Inequalities (OUP 2013), Ch. 3 (Efron-Stein).

import Mathlib.Probability.CondVar
import Mathlib.Probability.Moments.Variance
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

theorem variance_condExp_telescope
    {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : Measure[m₀] Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ)
    (F : ℕ → MeasurableSpace Ω) (hmono : Monotone F) (hle : ∀ k, F k ≤ m₀) :
    ∀ N, Var[μ[X | F N]; μ]
      = Var[μ[X | F 0]; μ]
        + ∑ k ∈ Finset.range N, μ[Var[μ[X | F (k+1)]; μ | F k]] := by sorry

-- Prove2me | Theorems.Thm_variance_eq_sum_expected_condVar
-- name    : variance_eq_sum_expected_condVar
-- status  : Proved
-- author  : @allychan327
-- created : 2026-06-24T01:37:46.6337+00:00
-- url     : https://prove2.me/theorems/d589c608-a1ab-4ef0-ab4a-b2b9a8adc6ee
-- statement:
--   **Exact Efron–Stein tensorization of variance (Doob-martingale form).** Let $F : \mathbb{N} \to$ (sub-$\sigma$-algebras of $m_0$) be a monotone filtration with $F_0 = \bot$ (the trivial $\sigma$-algebra) and $F_N = m_0$ (the full $\sigma$-algebra), and let $X$ be square-integrable. Then
--
--   $$\operatorname{Var}(X) = \sum_{k=0}^{N-1} \mathbb{E}\Big[\operatorname{Var}\big(\mathbb{E}[X \mid F_{k+1}] \mid F_k\big)\Big].$$
--
--   The total variance decomposes exactly into the sum, over the filtration steps, of the expected conditional variance contributed at each step. The boundary terms collapse: $\mathbb{E}[X\mid\bot]$ is the constant $\int X\,d\mu$ (variance $0$) and $\mathbb{E}[X\mid m_0] = X$ a.e. (variance $\operatorname{Var}(X)$). Specializing $F$ to a coordinate filtration on a product space yields the Efron–Stein tensorization, with each summand the variance contributed by coordinate $k$ — the inductive heart of the general (nonlinear) Efron–Stein inequality.
-- source:
--   R. van Handel, Probability in High Dimension (APC 550 lecture notes, Princeton), §2.1 Tensorization and bounded differences (Doob-martingale decomposition of variance); Boucheron-Lugosi-Massart, Concentration Inequalities (OUP 2013), Ch. 3 (Efron-Stein).

import Mathlib.Probability.CondVar
import Mathlib.Probability.Moments.Variance
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

theorem variance_eq_sum_expected_condVar
    {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : Measure[m₀] Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ)
    (F : ℕ → MeasurableSpace Ω) (hmono : Monotone F) (hle : ∀ k, F k ≤ m₀)
    (hbot : F 0 = ⊥) (N : ℕ) (htop : F N = m₀) :
    Var[X; μ]
      = ∑ k ∈ Finset.range N, μ[Var[μ[X | F (k+1)]; μ | F k]] := by sorry

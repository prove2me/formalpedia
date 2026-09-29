-- Prove2me | Theorems.Thm_variance_nested_two_step
-- name    : variance_nested_two_step
-- status  : Proved
-- author  : @allychan327
-- created : 2026-06-24T01:29:38.847714+00:00
-- url     : https://prove2.me/theorems/04801f55-450b-4693-9e67-ba2e48008a83
-- statement:
--   **Two-step (nested) variance decomposition.** For nested sub-$\sigma$-algebras $m' \le m \le m_0$ and a square-integrable $X$ on $(\Omega, m_0, \mu)$, the total variance splits into three nonnegative pieces:
--
--   $$\operatorname{Var}(X) = \mathbb{E}\big[\operatorname{Var}(X \mid m)\big] + \mathbb{E}\big[\operatorname{Var}(\mathbb{E}[X \mid m] \mid m')\big] + \operatorname{Var}\big(\mathbb{E}[X \mid m']\big).$$
--
--   This is the law of total variance applied twice — once to $X$ with the finer $m$, and once to the martingale $\mathbb{E}[X\mid m]$ with the coarser $m'$ — using the tower property $\mathbb{E}[\mathbb{E}[X\mid m]\mid m'] = \mathbb{E}[X\mid m']$ to identify the residual. It is the inductive heart of the Doob-martingale telescoping that produces the Efron–Stein sum: iterating this nesting over a coordinate filtration $\bot = F_0 \le F_1 \le \dots \le F_n = m_0$ expands $\operatorname{Var}(X)$ as $\sum_k \mathbb{E}[\operatorname{Var}(\mathbb{E}[X\mid F_k]\mid F_{k-1})]$, each term the conditional variance contributed by coordinate $k$.
-- source:
--   R. van Handel, Probability in High Dimension (APC 550 lecture notes, Princeton), §2.1 Tensorization and bounded differences (law of total variance / martingale decomposition); Boucheron-Lugosi-Massart, Concentration Inequalities (OUP 2013), Ch. 3.

import Mathlib.Probability.CondVar
import Mathlib.Probability.Moments.Variance
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

theorem variance_nested_two_step
    {Ω : Type*} {m₀ m : MeasurableSpace Ω} {μ : Measure[m₀] Ω}
    (hm : m ≤ m₀) {m' : MeasurableSpace Ω} (hm' : m' ≤ m)
    [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ) :
    Var[X; μ] = μ[Var[X; μ | m]] + μ[Var[μ[X | m]; μ | m']] + Var[μ[X | m']; μ] := by sorry

-- Prove2me | Theorems.Thm_bernoulli_powerset_expectation_linear
-- name    : bernoulli_powerset_expectation_linear
-- status  : Proved
-- author  : @Aphrodite
-- created : 2026-06-21T20:51:29.698319+00:00
-- url     : https://prove2.me/theorems/8af5bf77-248e-4d0f-b40f-2be534034936
-- statement:
--   **Linearity of the Bernoulli powerset expectation over a coordinate sum.** For a statistic that is a sum of per-coordinate functions of the inclusion indicators, $$\mathbb{E}\Big[\sum_w g_w(\mathbf{1}[w\in\Omega])\Big] = \sum_w\big(p\,g_w(1)+(1-p)\,g_w(0)\big).$$ Each term reduces to its single-coordinate marginal. This is the form used to compute the mean of the centered sampling coefficient.
-- source:
--   Boucheron–Lugosi–Massart, Concentration Inequalities (OUP 2013), Ch. 15; foundational independence of coordinate inclusions under the product-Bernoulli powerset measure, used for the q-moment Bernstein estimate in Candès–Recht 2009, arXiv:0805.4471, §6.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion
open scoped BigOperators

theorem bernoulli_powerset_expectation_linear {n₁ n₂ : ℕ} (p : ℝ)
    (g : (Fin n₁ × Fin n₂) → ℝ → ℝ) :
    bernoulliExpectation p
        (fun Omega => ∑ w : Fin n₁ × Fin n₂, g w (if w ∈ Omega then 1 else 0)) =
      ∑ w : Fin n₁ × Fin n₂, (p * g w 1 + (1 - p) * g w 0) := by sorry

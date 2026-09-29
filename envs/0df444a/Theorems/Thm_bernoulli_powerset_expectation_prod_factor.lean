-- Prove2me | Theorems.Thm_bernoulli_powerset_expectation_prod_factor
-- name    : bernoulli_powerset_expectation_prod_factor
-- status  : Proved
-- author  : @Aphrodite
-- created : 2026-06-21T20:50:48.347067+00:00
-- url     : https://prove2.me/theorems/bfb5eb90-7440-474c-b294-39593d56c784
-- statement:
--   **Independence / product factorization of the Bernoulli powerset expectation.** Under the powerset-Bernoulli measure with inclusion probability $p$ (each coordinate $w=(i,j)$ included independently with weight $p^{|\Omega|}(1-p)^{N-|\Omega|}$), for any family of per-coordinate functions $f_w:\mathbb{R}\to\mathbb{R}$ the expectation of the product factorizes: $$\mathbb{E}\Big[\prod_w f_w(\mathbf{1}[w\in\Omega])\Big] = \prod_w\big(p\,f_w(1)+(1-p)\,f_w(0)\big).$$ This is the precise statement that the coordinate inclusion indicators are independent. It is the foundational building block for computing moments (mean, variance, higher moments) of any statistic linear in the inclusion indicators, e.g. the centered sampling coefficient $\sum_{ij}p^{-1}(\mathbf{1}[(i,j)\in\Omega]-p)B_{ij}$.
-- source:
--   Boucheron–Lugosi–Massart, Concentration Inequalities (OUP 2013), Ch. 15; foundational independence of coordinate inclusions under the product-Bernoulli powerset measure, used for the q-moment Bernstein estimate in Candès–Recht 2009, arXiv:0805.4471, §6.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion
open scoped BigOperators

theorem bernoulli_powerset_expectation_prod_factor {n₁ n₂ : ℕ} (p : ℝ)
    (f : (Fin n₁ × Fin n₂) → ℝ → ℝ) :
    bernoulliExpectation p
        (fun Omega => ∏ w : Fin n₁ × Fin n₂, f w (if w ∈ Omega then 1 else 0)) =
      ∏ w : Fin n₁ × Fin n₂, (p * f w 1 + (1 - p) * f w 0) := by sorry

-- Prove2me | Theorems.Thm_bernoulli_powerset_expectation_single_coordinate
-- name    : bernoulli_powerset_expectation_single_coordinate
-- status  : Proved
-- author  : @Aphrodite
-- created : 2026-06-21T20:51:09.334342+00:00
-- url     : https://prove2.me/theorems/740c5573-294b-4a2b-8a2c-9bc108c6f15f
-- statement:
--   **Single-coordinate marginal of the Bernoulli powerset expectation.** For a statistic depending only on the inclusion of one fixed coordinate $w$, $$\mathbb{E}\big[g(\mathbf{1}[w\in\Omega])\big] = p\,g(1)+(1-p)\,g(0),$$ i.e. coordinate $w$ has marginal Bernoulli$(p)$ distribution. A direct consequence of the product-factorization (independence) lemma.
-- source:
--   Boucheron–Lugosi–Massart, Concentration Inequalities (OUP 2013), Ch. 15; foundational independence of coordinate inclusions under the product-Bernoulli powerset measure, used for the q-moment Bernstein estimate in Candès–Recht 2009, arXiv:0805.4471, §6.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion
open scoped BigOperators

theorem bernoulli_powerset_expectation_single_coordinate {n₁ n₂ : ℕ}
    (p : ℝ) (w : Fin n₁ × Fin n₂) (g : ℝ → ℝ) :
    bernoulliExpectation p (fun Omega => g (if w ∈ Omega then 1 else 0)) =
      p * g 1 + (1 - p) * g 0 := by sorry

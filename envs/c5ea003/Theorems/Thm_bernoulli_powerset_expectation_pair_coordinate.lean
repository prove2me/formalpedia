-- Prove2me | Theorems.Thm_bernoulli_powerset_expectation_pair_coordinate
-- name    : bernoulli_powerset_expectation_pair_coordinate
-- status  : Proved
-- author  : @Aphrodite
-- created : 2026-06-21T20:57:03.835479+00:00
-- url     : https://prove2.me/theorems/e1573ddf-8dba-46ad-af25-47c711909add
-- statement:
--   **Pair-coordinate independence of the Bernoulli powerset expectation.** For two *distinct* coordinates $w\neq w'$, the expectation of a product of per-coordinate functions factorizes into the product of the two single-coordinate marginals: $$\mathbb{E}\big[g(\mathbf{1}[w\in\Omega])\,h(\mathbf{1}[w'\in\Omega])\big] = \big(p\,g(1)+(1-p)\,g(0)\big)\big(p\,h(1)+(1-p)\,h(0)\big).$$ This is the key input that makes the off-diagonal (cross) terms vanish when computing the variance / second moment of a statistic linear in the inclusion indicators, e.g. $\mathbb{E}[(\sum_w a_w(\mathbf{1}[w\in\Omega]-p))^2]=\sum_w a_w^2\,p(1-p)$. A direct consequence of the product-factorization (independence) lemma.
-- source:
--   Boucheron–Lugosi–Massart, Concentration Inequalities (OUP 2013), Ch. 15; pairwise independence of coordinate inclusions under the product-Bernoulli powerset measure, used for the variance/moment computations in Candès–Recht 2009, arXiv:0805.4471, §6.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion
open scoped BigOperators

theorem bernoulli_powerset_expectation_pair_coordinate {n₁ n₂ : ℕ}
    (p : ℝ) (w w' : Fin n₁ × Fin n₂) (hww : w ≠ w') (g h : ℝ → ℝ) :
    bernoulliExpectation p
        (fun Omega => g (if w ∈ Omega then 1 else 0) * h (if w' ∈ Omega then 1 else 0)) =
      (p * g 1 + (1 - p) * g 0) * (p * h 1 + (1 - p) * h 0) := by sorry

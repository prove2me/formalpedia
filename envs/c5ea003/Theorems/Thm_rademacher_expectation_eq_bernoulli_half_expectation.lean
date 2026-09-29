-- Prove2me | Theorems.Thm_rademacher_expectation_eq_bernoulli_half_expectation
-- name    : rademacher_expectation_eq_bernoulli_half_expectation
-- status  : Proved
-- author  : @Aphrodite
-- created : 2026-06-23T17:24:59.550354+00:00
-- url     : https://prove2.me/theorems/a2fb59eb-6187-4f21-bc78-765f1a24c6c7
-- statement:
--   The uniform Rademacher-sign expectation equals the Bernoulli powerset expectation at inclusion probability $p = 1/2$: $\mathbb{E}_\varepsilon[F] = \mathbb{E}_{p=1/2}[F]$. Both are finite sums over $\mathrm{Finset}(\mathrm{Fin}\,n_1\times\mathrm{Fin}\,n_2)$; the Rademacher weight is the constant $(1/2)^N$ and the Bernoulli weight at $p=1/2$ is $(1/2)^{|\Omega|}(1/2)^{N-|\Omega|}=(1/2)^N$, so the weights coincide pointwise. This is the σ-fiber bridge that lets the Bernoulli powerset measure substrate apply to the symmetric sign measure of de la Peña–Montgomery-Smith 1995 §4.
-- source:
--   de la Peña–Montgomery-Smith, Ann. Probab. 23 (1995) 806–816 (arXiv:math/9309211), §4 (symmetric σ-signs = p=1/2 Bernoulli model)

import Definitions.Def_matrix_completion_rademacher
import Definitions.Def_matrix_completion_bernoulli
open MatrixCompletion
open scoped BigOperators Classical

theorem rademacher_expectation_eq_bernoulli_half_expectation {n1 n2 : ℕ} (F : Finset (Fin n1 × Fin n2) → ℝ) : rademacherExpectation F = bernoulliExpectation ((1 : ℝ) / 2) F := by sorry

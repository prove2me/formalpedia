-- Prove2me | Theorems.Thm_schatten_norm_nonneg
-- name    : schatten_norm_nonneg
-- status  : Proved
-- author  : @Aphrodite
-- created : 2026-06-21T17:39:52.337699+00:00
-- url     : https://prove2.me/theorems/4258c7e8-9491-43ab-a0d7-e4e982e5cb34
-- statement:
--   The Schatten $q$-norm $\|X\|_{S_q} = (\sum_k \sigma_k(X)^q)^{1/q}$ of any real matrix $X$ is nonnegative, for every real exponent $q$. This is immediate from nonnegativity of the singular values and of the real power function on nonnegative arguments.
-- source:
--   Candès–Recht 2009, Exact Matrix Completion via Convex Optimization, arXiv:0805.4471, §6.1 (Schatten-norm comparison preliminaries), p.24-25. Basic Schatten S_q-norm API fact on Mathlib LinearMap.singularValues.

import Definitions.Def_matrix_completion_schatten
open MatrixCompletion
open scoped BigOperators

theorem schatten_norm_nonneg : ∀ {n₁ n₂ : ℕ} (q : ℝ) (X : Matrix (Fin n₁) (Fin n₂) ℝ), 0 ≤ schattenNorm q X := by sorry

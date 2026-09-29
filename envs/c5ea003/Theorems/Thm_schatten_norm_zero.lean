-- Prove2me | Theorems.Thm_schatten_norm_zero
-- name    : schatten_norm_zero
-- status  : Proved
-- author  : @Aphrodite
-- created : 2026-06-21T17:40:13.924359+00:00
-- url     : https://prove2.me/theorems/3e893b05-8ce9-4990-8d99-3804d809dfd6
-- statement:
--   The Schatten $q$-norm of the zero matrix is zero, for any nonzero real exponent $q$. The zero linear map has all singular values equal to zero, so the defining sum vanishes and $(0)^{1/q} = 0$.
-- source:
--   Candès–Recht 2009, Exact Matrix Completion via Convex Optimization, arXiv:0805.4471, §6.1 (Schatten-norm comparison preliminaries), p.24-25. Basic Schatten S_q-norm API fact on Mathlib LinearMap.singularValues.

import Definitions.Def_matrix_completion_schatten
open MatrixCompletion
open scoped BigOperators

theorem schatten_norm_zero : ∀ {n₁ n₂ : ℕ} (q : ℝ), q ≠ 0 → schattenNorm q (0 : Matrix (Fin n₁) (Fin n₂) ℝ) = 0 := by sorry

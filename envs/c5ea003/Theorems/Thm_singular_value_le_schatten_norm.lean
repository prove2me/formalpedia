-- Prove2me | Theorems.Thm_singular_value_le_schatten_norm
-- name    : singular_value_le_schatten_norm
-- status  : Proved
-- author  : @Aphrodite
-- created : 2026-06-21T17:40:34.55902+00:00
-- url     : https://prove2.me/theorems/09aaee32-7424-4475-a2b3-ccb959f2b67c
-- statement:
--   For $q \ge 1$, every singular value $\sigma_k(X)$ (indexed within $\mathrm{Fin}\,n_2$) of a real matrix $X$ is bounded by its Schatten $q$-norm: $\sigma_k(X) = (\sigma_k(X)^q)^{1/q} \le (\sum_j \sigma_j(X)^q)^{1/q} = \|X\|_{S_q}$. This generalizes the operator-norm bound (the $k=0$ top-singular-value case) to every singular value.
-- source:
--   Candès–Recht 2009, Exact Matrix Completion via Convex Optimization, arXiv:0805.4471, §6.1 (Schatten-norm comparison preliminaries), p.24-25. Basic Schatten S_q-norm API fact on Mathlib LinearMap.singularValues.

import Definitions.Def_matrix_completion_schatten
import Mathlib.Analysis.SpecialFunctions.Pow.Real
open MatrixCompletion
open scoped BigOperators

theorem singular_value_le_schatten_norm : ∀ {n₁ n₂ : ℕ} (q : ℝ) (X : Matrix (Fin n₁) (Fin n₂) ℝ) (k : Fin n₂), 1 ≤ q → (Matrix.toEuclideanLin X).singularValues (k : ℕ) ≤ schattenNorm q X := by sorry

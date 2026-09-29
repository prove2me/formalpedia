-- Prove2me | Theorems.Thm_nonempty_closed_matrix_set_has_frobenius_sq_minimizer
-- name    : nonempty_closed_matrix_set_has_frobenius_sq_minimizer
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-22T08:09:33.461298+00:00
-- url     : https://prove2.me/theorems/da7bad4d-866d-483d-b5c6-32a2f1b7428b
-- statement:
--   This is the finite-dimensional optimization lemma behind the least-squares certificate problem.
--
--   For matrices $Y\in\mathbb R^{n_1\times n_2}$, let
--   $$
--   \|Y\|_F^2=\sum_{i,j}Y_{ij}^2.
--   $$
--   The theorem says that if $C$ is a nonempty closed subset of this finite-dimensional matrix space, then there exists $Y\in C$ such that
--   $$
--   \|Y\|_F^2\le \|Z\|_F^2\qquad\text{for every }Z\in C.
--   $$
--   This packages the coercivity/properness argument for the Frobenius norm in finite dimensions.  In the Candes-Recht proof it is used for the feasible affine set in equation (4.1).
--
--   Source: formal finite-dimensional optimization bridge for Candes-Recht 2008, PDF p. 17, equation (4.1).
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Mathlib.Tactic
import Definitions.Def_matrix_completion_tangent
open MatrixCompletion

theorem nonempty_closed_matrix_set_has_frobenius_sq_minimizer
    {n₁ n₂ : ℕ} (C : Set (Matrix (Fin n₁) (Fin n₂) ℝ)) :
    C.Nonempty → IsClosed C →
    ∃ Y : Matrix (Fin n₁) (Fin n₂) ℝ,
      Y ∈ C ∧ ∀ Z : Matrix (Fin n₁) (Fin n₂) ℝ,
        Z ∈ C → frobeniusNormSq Y ≤ frobeniusNormSq Z := by
  sorry

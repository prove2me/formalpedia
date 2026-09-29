-- Prove2me | Theorems.Thm_svd_singular_coordinate_energy_le_one
-- name    : svd_singular_coordinate_energy_le_one
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-21T17:04:54.183306+00:00
-- url     : https://prove2.me/theorems/b557d2a5-542b-4350-b858-173bea53d2ce
-- statement:
--   This is the Bessel-type bound for the raw orthonormal singular-vector families carried by the project's `SVD` structure.
--
--   For every coordinate $i$ and $j$,
--   $$
--   \sum_{k=1}^r u_k(i)^2\le 1,\qquad
--   \sum_{k=1}^r v_k(j)^2\le 1.
--   $$
--   It follows only from orthonormality of the singular vectors. This is the linear-algebra ingredient used when bounding the diagonal tangent-coordinate kernel.
--
--   Source: standard finite-dimensional Bessel inequality for an orthonormal family; used in Candes-Recht 2008, PDF p. 23, estimate (6.2).
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion
open scoped Classical BigOperators

theorem svd_singular_coordinate_energy_le_one
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) :
      (∀ i : Fin n₁, ∑ k : Fin r, (S.u k i) ^ 2 ≤ (1 : ℝ)) ∧
      (∀ j : Fin n₂, ∑ k : Fin r, (S.v k j) ^ 2 ≤ (1 : ℝ)) := by
  sorry

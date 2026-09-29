-- Prove2me | Theorems.Thm_quadratic_neumann_middle_index_distinct_mean_as_off_diagonal_response
-- name    : quadratic_neumann_middle_index_distinct_mean_as_off_diagonal_response
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-01T14:21:47.464252+00:00
-- url     : https://prove2.me/theorems/280e7ac2-2e77-43cf-bbd7-40039bd163ef
-- statement:
--   Deterministic identity from Candes-Recht Section 6.3: the middle-index mean contribution equals `(1-p)` times the middle off-diagonal response applied to the centered fluctuation of the rescaled all-ones matrix. This is a pure expansion of equation (6.20).
-- source:
--   Candes-Recht 2008, Section 6.3, PDF pp. 32--33, equation (6.20).

import Definitions.Def_matrix_completion_neumann_middle_response
open MatrixCompletion

theorem quadratic_neumann_middle_index_distinct_mean_as_off_diagonal_response
    {n₁ n₂ r : Nat} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega : Finset (Fin n₁ × Fin n₂)) (S : SVD M r) (p : ℝ) :
    quadraticNeumannMiddleIndexDistinctMeanContribution Omega S p =
      (1 - p) •
        quadraticMiddleIndexDistinctOffDiagonalResponse S
          (centeredSamplingFluctuation Omega p (p⁻¹ • onesMatrix n₁ n₂)) := by sorry

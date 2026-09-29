-- Prove2me | solution 2 for quadratic_neumann_middle_index_distinct_centered_diagonal_decoupled_equals_original
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-20T20:14:22.224123+00:00
-- url     : https://prove2.me/submissions/3d19231d-d8aa-44ee-85db-13127a3a08fd

import Definitions.Def_matrix_completion_neumann

open MatrixCompletion

theorem solution
    {n₁ n₂ r : Nat} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega : Finset (Fin n₁ × Fin n₂)) (S : SVD M r) (p : ℝ) :
    quadraticNeumannMiddleIndexDistinctCenteredDecoupledContribution Omega Omega S p =
      quadraticNeumannMiddleIndexDistinctCenteredContribution Omega S p := by
  rfl


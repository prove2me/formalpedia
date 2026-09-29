-- Prove2me | solution 2 for linear_neumann_off_diagonal_diagonal_decoupled_equals_original
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-20T20:14:21.440983+00:00
-- url     : https://prove2.me/submissions/89bda5a6-1dea-43de-8e58-d0709bfff5a9

import Definitions.Def_matrix_completion_neumann

open MatrixCompletion

theorem solution
    {n₁ n₂ r : Nat} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega : Finset (Fin n₁ × Fin n₂)) (S : SVD M r) (p : ℝ) :
    linearNeumannOffDiagonalDecoupledContribution Omega Omega S p =
      linearNeumannOffDiagonalContribution Omega S p := by
  rfl


-- Prove2me | solution 1 for linear_neumann_off_diagonal_diagonal_decoupled_equals_original
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-06-20T15:44:27.459012+00:00
-- url     : https://prove2.me/submissions/4f18957f-0e50-4191-af18-9b297f20a187

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem solution
    {n₁ n₂ r : Nat} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega : Finset (Fin n₁ × Fin n₂)) (S : SVD M r) (p : ℝ) :
    linearNeumannOffDiagonalDecoupledContribution Omega Omega S p =
      linearNeumannOffDiagonalContribution Omega S p := by
  rfl

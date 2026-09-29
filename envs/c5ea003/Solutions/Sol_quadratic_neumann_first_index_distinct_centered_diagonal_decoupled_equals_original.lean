-- Prove2me | solution 1 for quadratic_neumann_first_index_distinct_centered_diagonal_decoupled_equals_original
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-06-20T15:45:47.792611+00:00
-- url     : https://prove2.me/submissions/8649a567-0e35-4d55-9fef-4109c6170fbe

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem solution
    {n₁ n₂ r : Nat} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega : Finset (Fin n₁ × Fin n₂)) (S : SVD M r) (p : ℝ) :
    quadraticNeumannFirstIndexDistinctCenteredDecoupledContribution Omega Omega S p =
      quadraticNeumannFirstIndexDistinctCenteredContribution Omega S p := by
  rfl

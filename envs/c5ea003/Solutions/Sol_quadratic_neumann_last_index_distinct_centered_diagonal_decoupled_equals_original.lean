-- Prove2me | solution 1 for quadratic_neumann_last_index_distinct_centered_diagonal_decoupled_equals_original
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-06-20T15:46:24.924414+00:00
-- url     : https://prove2.me/submissions/c23c9041-6f1d-4af7-9a27-f5a250d9a255

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem solution
    {n₁ n₂ r : Nat} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega : Finset (Fin n₁ × Fin n₂)) (S : SVD M r) (p : ℝ) :
    quadraticNeumannLastIndexDistinctCenteredDecoupledContribution Omega Omega S p =
      quadraticNeumannLastIndexDistinctCenteredContribution Omega S p := by
  rfl

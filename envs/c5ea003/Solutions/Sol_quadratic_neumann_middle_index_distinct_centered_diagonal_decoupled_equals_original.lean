-- Prove2me | solution 1 for quadratic_neumann_middle_index_distinct_centered_diagonal_decoupled_equals_original
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-06-20T15:47:02.279494+00:00
-- url     : https://prove2.me/submissions/8ac4d3ba-d2ba-494e-b71e-8b2419993a67

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem solution
    {n₁ n₂ r : Nat} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega : Finset (Fin n₁ × Fin n₂)) (S : SVD M r) (p : ℝ) :
    quadraticNeumannMiddleIndexDistinctCenteredDecoupledContribution Omega Omega S p =
      quadraticNeumannMiddleIndexDistinctCenteredContribution Omega S p := by
  rfl

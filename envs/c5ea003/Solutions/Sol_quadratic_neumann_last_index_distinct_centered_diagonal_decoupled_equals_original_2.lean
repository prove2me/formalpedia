-- Prove2me | solution 2 for quadratic_neumann_last_index_distinct_centered_diagonal_decoupled_equals_original
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-20T20:14:22.520225+00:00
-- url     : https://prove2.me/submissions/572ed049-790c-43b5-8507-f35d0b56b508

import Definitions.Def_matrix_completion_neumann

open MatrixCompletion

theorem solution
    {n₁ n₂ r : Nat} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega : Finset (Fin n₁ × Fin n₂)) (S : SVD M r) (p : ℝ) :
    quadraticNeumannLastIndexDistinctCenteredDecoupledContribution Omega Omega S p =
      quadraticNeumannLastIndexDistinctCenteredContribution Omega S p := by
  rfl


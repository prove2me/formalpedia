-- Prove2me | solution 2 for quadratic_neumann_first_index_distinct_centered_diagonal_decoupled_equals_original
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-20T20:14:21.918937+00:00
-- url     : https://prove2.me/submissions/5b0c22b1-b123-4ce2-a15c-b56b4e7baa45

import Definitions.Def_matrix_completion_neumann

open MatrixCompletion

theorem solution
    {n₁ n₂ r : Nat} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega : Finset (Fin n₁ × Fin n₂)) (S : SVD M r) (p : ℝ) :
    quadraticNeumannFirstIndexDistinctCenteredDecoupledContribution Omega Omega S p =
      quadraticNeumannFirstIndexDistinctCenteredContribution Omega S p := by
  rfl


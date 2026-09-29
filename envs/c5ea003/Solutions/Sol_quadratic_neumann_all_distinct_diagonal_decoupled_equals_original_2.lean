-- Prove2me | solution 2 for quadratic_neumann_all_distinct_diagonal_decoupled_equals_original
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-20T20:14:22.848047+00:00
-- url     : https://prove2.me/submissions/be58e6cd-37c7-434d-80cd-d4f803279340

import Definitions.Def_matrix_completion_neumann

open MatrixCompletion

theorem solution
    {n₁ n₂ r : Nat} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega : Finset (Fin n₁ × Fin n₂)) (S : SVD M r) (p : ℝ) :
    quadraticNeumannAllDistinctDecoupledContribution Omega Omega Omega S p =
      quadraticNeumannAllDistinctContribution Omega S p := by
  rfl


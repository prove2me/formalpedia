-- Prove2me | solution 1 for quadratic_neumann_all_distinct_diagonal_decoupled_equals_original
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-06-20T15:45:05.072829+00:00
-- url     : https://prove2.me/submissions/f6f5efbf-d53a-4103-a34f-42cb8dcf0a7e

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem solution
    {n₁ n₂ r : Nat} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega : Finset (Fin n₁ × Fin n₂)) (S : SVD M r) (p : ℝ) :
    quadraticNeumannAllDistinctDecoupledContribution Omega Omega Omega S p =
      quadraticNeumannAllDistinctContribution Omega S p := by
  rfl

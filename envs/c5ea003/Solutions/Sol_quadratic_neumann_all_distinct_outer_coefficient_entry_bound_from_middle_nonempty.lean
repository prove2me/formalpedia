-- Prove2me | solution 1 for quadratic_neumann_all_distinct_outer_coefficient_entry_bound_from_middle_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-21T05:31:25.613727+00:00
-- url     : https://prove2.me/submissions/4fa1c4fe-2eee-4415-aa14-d6c08cbf4cb1

import Definitions.Def_matrix_completion_neumann

open MatrixCompletion

theorem solution
    {n₁ n₂ r : Nat} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega2 Omega3 : Finset (Fin n₁ × Fin n₂)) (S : SVD M r)
    (p bound : ℝ) :
    0 < n₁ → 0 < n₂ →
    QuadraticAllDistinctMiddleCoefficientBound Omega2 Omega3 S p bound →
      entrySupNorm
          (quadraticAllDistinctOuterCoefficientMatrix Omega2 Omega3 S p) ≤
        bound := by
  intro hn₁ hn₂ hMiddle
  haveI : Nonempty (Fin n₁) := ⟨⟨0, hn₁⟩⟩
  haveI : Nonempty (Fin n₂) := ⟨⟨0, hn₂⟩⟩
  unfold entrySupNorm quadraticAllDistinctOuterCoefficientMatrix
  apply ciSup_le
  intro i
  apply ciSup_le
  intro j
  exact hMiddle (i, j)

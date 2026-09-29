-- Prove2me | solution 3 for supported_matrix_inner_zero_of_zero_sampling_projection
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-20T20:14:20.831296+00:00
-- url     : https://prove2.me/submissions/d372b70f-b215-426a-9d2b-16171d9e074c

import Definitions.Def_matrix_completion_tangent

open MatrixCompletion

theorem solution
    {n₁ n₂ : ℕ} (Omega : Finset (Fin n₁ × Fin n₂))
    (Y H : Matrix (Fin n₁) (Fin n₂) ℝ) :
    VanishesOutside Omega Y →
    samplingProjection Omega H = 0 →
    matrixInner Y H = 0 := by
  intro hY hH
  unfold matrixInner
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  by_cases hmem : (i, j) ∈ Omega
  · have hHij : H i j = 0 := by
      have hentry :=
        congrArg (fun A : Matrix (Fin n₁) (Fin n₂) ℝ => A i j) hH
      simpa [samplingProjection, hmem] using hentry
    simp [hHij]
  · have hYij : Y i j = 0 := hY i j hmem
    simp [hYij]


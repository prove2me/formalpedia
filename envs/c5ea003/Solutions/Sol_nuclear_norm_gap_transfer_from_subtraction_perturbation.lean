-- Prove2me | solution 1 for nuclear_norm_gap_transfer_from_subtraction_perturbation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-15T15:18:49.123056+00:00
-- url     : https://prove2.me/submissions/c769446e-d2ca-4a8c-92f7-4e97823c24c6

import Theorems.Thm_nuclear_norm_gap_transfer_from_subtraction_perturbation

open MatrixCompletion

theorem solution
    {n₁ n₂ : ℕ} (X M : Matrix (Fin n₁) (Fin n₂) ℝ) :
    nuclearNorm M < nuclearNorm (M + (X - M)) →
    nuclearNorm M < nuclearNorm X := by
  intro hgap
  have hmatrix : M + (X - M) = X := by
    ext i j
    simp [sub_eq_add_neg, add_left_comm]
  simpa [hmatrix] using hgap

-- Prove2me | solution 1 for schatten_norm_zero
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-21T17:41:13.6618+00:00
-- url     : https://prove2.me/submissions/8547b73d-188e-466f-92e8-f4f300f09ea1

import Definitions.Def_matrix_completion_schatten

open MatrixCompletion
open scoped BigOperators

theorem solution :
    ∀ {n₁ n₂ : ℕ} (q : ℝ), q ≠ 0 →
      schattenNorm q (0 : Matrix (Fin n₁) (Fin n₂) ℝ) = 0 := by
  intro n₁ n₂ q hq
  unfold schattenNorm
  have h0 : (Matrix.toEuclideanLin (0 : Matrix (Fin n₁) (Fin n₂) ℝ)) = 0 := by simp
  rw [h0, LinearMap.singularValues_zero]
  have hsum : (∑ _k : Fin n₂, Real.rpow ((0 : ℕ →₀ ℝ) _k) q) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    simp [Real.zero_rpow hq]
  rw [hsum]
  exact Real.zero_rpow (inv_ne_zero hq)

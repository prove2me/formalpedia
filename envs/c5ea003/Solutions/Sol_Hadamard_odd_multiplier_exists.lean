-- Prove2me | solution 1 for Hadamard.odd_multiplier_exists
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-07T01:07:10.288375+00:00
-- url     : https://prove2.me/submissions/1c8ac5a7-bff2-4cbb-9ace-91117984bad1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Theorems.Thm_Hadamard_exists_orthogonal_pm_one

open Matrix

namespace HadBridge

/-- A Hadamard matrix in the orthogonality formulation has the extremal determinant. -/
lemma abs_det_of_orthogonal {n : ℕ} (hn : 0 < n) (M : Matrix (Fin n) (Fin n) ℝ)
    (horth : M * Mᵀ = (n : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)) :
    |M.det| = (n : ℝ) ^ ((n : ℝ) / 2) := by
  have hnn : (0:ℝ) ≤ (n : ℝ) := by positivity
  -- `(det M)^2 = n^n`
  have hdet2 : M.det ^ 2 = (n : ℝ) ^ n := by
    have h := congrArg Matrix.det horth
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_smul, Matrix.det_one,
      Fintype.card_fin, mul_one] at h
    rw [← h]; ring
  calc |M.det| = Real.sqrt (M.det ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ = Real.sqrt ((n : ℝ) ^ n) := by rw [hdet2]
    _ = (n : ℝ) ^ ((n : ℝ) / 2) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast ((n : ℝ)) n, ← Real.rpow_mul hnn]
        norm_num
        ring_nf

end HadBridge

open HadBridge

theorem solution (k : ℕ) (hk : Odd k) :
    ∃ M : Matrix (Fin (4 * k)) (Fin (4 * k)) ℝ,
      (∀ i j, M i j ∈ ({1, -1} : Finset ℝ)) ∧
      |M.det| = ((4 * k : ℕ) : ℝ) ^ (((4 * k : ℕ) : ℝ) / 2) := by
  obtain ⟨M, hpm, horth⟩ := Hadamard.exists_orthogonal_pm_one k hk
  refine ⟨M, hpm, ?_⟩
  have hk0 : 0 < k := by rcases hk with ⟨t, rfl⟩; omega
  exact abs_det_of_orthogonal (by omega) M horth

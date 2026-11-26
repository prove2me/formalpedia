-- Prove2me | solution 1 for ReweightedNPMLE.det_one_add_posSemidef_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:59:25.042205+00:00
-- url     : https://prove2.me/submissions/8854929d-2bda-4563-9643-5eb892d92c24

import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic

/-!
# Determinant monotonicity for sensitivity matrices

This file supplies the positive-definite determinant comparison used in the
paper's support--sensitivity argument.  Mathlib provides the spectral theorem
and positivity of eigenvalues; the two lemmas below package them into the
Loewner monotonicity statement needed by the Jacobian estimate.
-/

open Matrix
open scoped MatrixOrder
/-- Adding a positive-semidefinite matrix to the identity cannot decrease its
determinant. -/
theorem solution
    {n : Type*} [Fintype n] [DecidableEq n]
    {C : Matrix n n ℝ} (hC : C.PosSemidef) :
    1 ≤ (1 + C).det := by
  let U := hC.isHermitian.eigenvectorUnitary
  let D : Matrix n n ℝ := diagonal hC.isHermitian.eigenvalues
  have hspec : C = U * D * star (U : Matrix n n ℝ) := by
    simpa [U, D, Unitary.conjStarAlgAut_apply] using hC.isHermitian.spectral_theorem
  have hunit : (U : Matrix n n ℝ) * star (U : Matrix n n ℝ) = 1 :=
    Unitary.coe_mul_star_self U
  have hdet : (1 + C).det = (1 + D).det := by
    rw [hspec]
    have heq : (1 : Matrix n n ℝ) +
        (U : Matrix n n ℝ) * D * star (U : Matrix n n ℝ) =
        (U : Matrix n n ℝ) * (1 + D) * star (U : Matrix n n ℝ) := by
      calc
        (1 : Matrix n n ℝ) + (U : Matrix n n ℝ) * D * star (U : Matrix n n ℝ) =
            (U : Matrix n n ℝ) * 1 * star (U : Matrix n n ℝ) +
              U * D * star (U : Matrix n n ℝ) := by rw [Matrix.mul_one, hunit]
        _ = (U : Matrix n n ℝ) * (1 + D) * star (U : Matrix n n ℝ) := by
          noncomm_ring
    rw [heq, Matrix.det_mul, Matrix.det_mul]
    calc
      (U : Matrix n n ℝ).det * (1 + D).det * (star (U : Matrix n n ℝ)).det =
          ((U : Matrix n n ℝ).det * (star (U : Matrix n n ℝ)).det) *
            (1 + D).det := by ring
      _ = ((U : Matrix n n ℝ) * star (U : Matrix n n ℝ)).det * (1 + D).det := by
        rw [Matrix.det_mul]
      _ = (1 + D).det := by rw [hunit, Matrix.det_one, one_mul]
  rw [hdet]
  rw [show (1 + D) = diagonal (fun i ↦ 1 + hC.isHermitian.eigenvalues i) by
    classical
    ext i j
    by_cases hij : i = j
    · subst j
      simp [D]
    · simp [D, hij]]
  rw [det_diagonal]
  apply Finset.one_le_prod
  intro i hi
  linarith [hC.eigenvalues_nonneg i]

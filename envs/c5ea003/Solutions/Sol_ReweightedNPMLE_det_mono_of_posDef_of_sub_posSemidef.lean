-- Prove2me | solution 1 for ReweightedNPMLE.det_mono_of_posDef_of_sub_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:00:13.045068+00:00
-- url     : https://prove2.me/submissions/8e7b3d84-8b0b-4b81-b66d-faecd8ef3f79

import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic
import Theorems.Thm_ReweightedNPMLE_det_one_add_posSemidef_ge_one

/-!
# Determinant monotonicity for sensitivity matrices

This file supplies the positive-definite determinant comparison used in the
paper's support--sensitivity argument.  Mathlib provides the spectral theorem
and positivity of eigenvalues; the two lemmas below package them into the
Loewner monotonicity statement needed by the Jacobian estimate.
-/

open Matrix
open scoped MatrixOrder

open ReweightedNPMLE
open ReweightedNPMLE in
/-- Determinant is monotone in Loewner order above a positive-definite base. -/
theorem solution
    {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℝ} (hA : A.PosDef) (hBA : (B - A).PosSemidef) :
    A.det ≤ B.det := by
  let C := B - A
  let S := CFC.sqrt A
  have hSnonneg : (0 : Matrix n n ℝ) ≤ S := CFC.sqrt_nonneg A
  have hSpsd : S.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hSnonneg
  have hSinvHerm : (S⁻¹)ᴴ = S⁻¹ := hSpsd.isHermitian.inv.eq
  have hCconj : (S⁻¹ * C * S⁻¹).PosSemidef := by
    have h := hBA.conjTranspose_mul_mul_same S⁻¹
    rw [hSinvHerm] at h
    exact h
  have hsq : S * S = A := by
    simpa [S, pow_two] using CFC.sq_sqrt A
  have hinv : A⁻¹ = S⁻¹ * S⁻¹ := by
    rw [← hsq, Matrix.mul_inv_rev]
  have hone : 1 ≤ (1 + A⁻¹ * C).det := by
    rw [hinv, Matrix.mul_assoc,
      Matrix.det_one_add_mul_comm S⁻¹ (S⁻¹ * C)]
    exact det_one_add_posSemidef_ge_one hCconj
  have hAunitdet : IsUnit A.det := A.isUnit_iff_isUnit_det.mp hA.isUnit
  have hfactor : B.det = A.det * (1 + A⁻¹ * C).det := by
    have hB : B = A + C * (1 : Matrix n n ℝ) := by simp [C]
    rw [hB, Matrix.det_add_mul C 1 hAunitdet]
    simp
  rw [hfactor]
  exact (le_mul_iff_one_le_right hA.det_pos).2 hone

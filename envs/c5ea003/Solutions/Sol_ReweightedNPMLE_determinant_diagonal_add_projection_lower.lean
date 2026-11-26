-- Prove2me | solution 1 for ReweightedNPMLE.determinant_diagonal_add_projection_lower
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:01:21.26296+00:00
-- url     : https://prove2.me/submissions/f10f1f0c-7c97-4a09-85c4-2131cfd1b2e7

import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic
import Theorems.Thm_ReweightedNPMLE_det_mono_of_posDef_of_sub_posSemidef

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
/-- The quantitative determinant gain from an orthonormal family of
sensitivity directions.  The upper diagonal bound `9/8` gives the inverse
bound `8/9`; adding the identity therefore contributes `17/9` in every
direction. -/
theorem solution
    {n k : Type*} [Fintype n] [DecidableEq n]
    [Fintype k] [DecidableEq k]
    (a : n → ℝ) (ha0 : ∀ i, 0 < a i) (haUpper : ∀ i, a i ≤ 9 / 8)
    (V : Matrix n k ℝ) (hV : Vᴴ * V = 1) :
    (∏ i, a i) * (17 / 9 : ℝ) ^ Fintype.card k ≤
      (diagonal a + V * Vᴴ).det := by
  let A : Matrix n n ℝ := diagonal a
  let G : Matrix k k ℝ := Vᴴ * A⁻¹ * V
  let c : ℝ := 8 / 9
  have hApos : A.PosDef := by
    dsimp [A]
    rw [Matrix.posDef_diagonal_iff]
    exact ha0
  have haunit : IsUnit a := Pi.isUnit_iff.mpr fun i ↦
    isUnit_iff_ne_zero.mpr (ha0 i).ne'
  have hAdiag : A.det = ∏ i, a i := by simp [A, Matrix.det_diagonal]
  have hAinvLower : (A⁻¹ - c • (1 : Matrix n n ℝ)).PosSemidef := by
    have heq : A⁻¹ - c • (1 : Matrix n n ℝ) =
        diagonal (fun i ↦ (a i)⁻¹ - c) := by
      classical
      ext i j
      by_cases hij : i = j
      · subst j
        simp only [A, Matrix.inv_diagonal, Matrix.sub_apply, Matrix.diagonal_apply_eq,
          Matrix.smul_apply, Matrix.one_apply_eq]
        rw [Ring.inverse_of_isUnit haunit, haunit.val_inv_apply]
        simp
      · simp [A, c, Matrix.inv_diagonal, hij]
    rw [heq]
    apply Matrix.PosSemidef.diagonal
    intro i
    have hinv : c ≤ (a i)⁻¹ := by
      rw [show (a i)⁻¹ = 1 / a i by simp, le_div_iff₀ (ha0 i)]
      dsimp [c]
      nlinarith [haUpper i]
    exact sub_nonneg.mpr hinv
  have hGsub : (G - c • (1 : Matrix k k ℝ)).PosSemidef := by
    have h := hAinvLower.conjTranspose_mul_mul_same V
    have hscalar : Vᴴ * (c • (1 : Matrix n n ℝ)) * V =
        c • (1 : Matrix k k ℝ) := by
      rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hV]
    have heq : Vᴴ * (A⁻¹ - c • (1 : Matrix n n ℝ)) * V =
        G - c • (1 : Matrix k k ℝ) := by
      dsimp [G]
      calc
        Vᴴ * (A⁻¹ - c • (1 : Matrix n n ℝ)) * V =
            Vᴴ * A⁻¹ * V - Vᴴ * (c • (1 : Matrix n n ℝ)) * V := by
          rw [Matrix.mul_sub, Matrix.sub_mul]
        _ = Vᴴ * A⁻¹ * V - c • (1 : Matrix k k ℝ) := by rw [hscalar]
    rw [heq] at h
    exact h
  have hbase : (1 + c • (1 : Matrix k k ℝ)).PosDef := by
    have heq : (1 + c • (1 : Matrix k k ℝ)) =
        diagonal (fun _ ↦ 1 + c) := by
      classical
      ext i j
      by_cases hij : i = j
      · subst j
        simp [c]
      · simp [hij]
    rw [heq, Matrix.posDef_diagonal_iff]
    intro i
    norm_num [c]
  have horder : ((1 + G) - (1 + c • (1 : Matrix k k ℝ))).PosSemidef := by
    have heq : (1 + G) - (1 + c • (1 : Matrix k k ℝ)) =
        G - c • (1 : Matrix k k ℝ) := by abel
    rw [heq]
    exact hGsub
  have hdetG : (17 / 9 : ℝ) ^ Fintype.card k ≤ (1 + G).det := by
    have hmono := det_mono_of_posDef_of_sub_posSemidef hbase horder
    have hbaseDet : (1 + c • (1 : Matrix k k ℝ)).det =
        (17 / 9 : ℝ) ^ Fintype.card k := by
      have heq : (1 + c • (1 : Matrix k k ℝ)) =
          diagonal (fun _ ↦ (17 / 9 : ℝ)) := by
        classical
        ext i j
        by_cases hij : i = j
        · subst j
          norm_num [c]
        · simp [hij]
      rw [heq, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ]
    rwa [hbaseDet] at hmono
  have hfactor : (diagonal a + V * Vᴴ).det = (∏ i, a i) * (1 + G).det := by
    have hAunitdet : IsUnit A.det := A.isUnit_iff_isUnit_det.mp hApos.isUnit
    have h := Matrix.det_add_mul V Vᴴ hAunitdet
    rw [hAdiag] at h
    simpa [A, G] using h
  rw [hfactor]
  exact mul_le_mul_of_nonneg_left hdetG
    (Finset.prod_nonneg fun i _ ↦ (ha0 i).le)
